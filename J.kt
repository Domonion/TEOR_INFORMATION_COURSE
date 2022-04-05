import java.io.FileInputStream
import java.io.PrintStream
import java.lang.IllegalStateException
import java.math.BigInteger
import kotlin.random.Random
import kotlin.random.asJavaRandom

val ZERO: BigInteger = BigInteger.ZERO
val ONE: BigInteger = BigInteger.ONE
val TWO: BigInteger = BigInteger.TWO

fun maxBit(number: BigInteger): BigInteger {
    var pos = ZERO
    var current = number.shr(1)

    while (current != ZERO) {
        pos = pos + ONE
        current = current.shr(1)
    }

    return pos
}

fun testBit(x: BigInteger, n: BigInteger): Boolean {
    return x.testBit(n.toInt())
}

fun BigInteger.shl(other: BigInteger): BigInteger {
    return this.shl(other.toInt())
}

fun pow2(power: BigInteger): BigInteger {
    return TWO.pow(power.toInt())
}

fun <T : Any> T.repeat2(times: Int? = null): Sequence<T> = sequence {
    var count = 0
    while (times == null || count++ < times) yield(this@repeat2)
}

fun <T : Any> List<T>.getAllSubsets(r: Int, replace: Boolean = false): Sequence<List<T>> {
    val n = count()
    if (r > n) return sequenceOf()
    return sequence {
        var indices = if (replace) 0.repeat2(r).toMutableList() else (0 until r).toMutableList()
        while (true) {
            yield(indices.map { this@getAllSubsets[it] })
            var i = r - 1
            loop@ while (i >= 0) {
                when (replace) {
                    true -> if (indices[i] != n - 1) break@loop
                    false -> if (indices[i] != i + n - r) break@loop
                }
                i--
            }
            if (i < 0) break
            when (replace) {
                true -> indices = (indices.take(i) + (indices[i] + 1).repeat2(r - i)).toMutableList()
                false -> {
                    indices[i] += 1
                    (i + 1 until r).forEach { indices[it] = indices[it - 1] + 1 }
                }
            }
        }
    }
}

fun bitIndices(number: BigInteger): MutableList<BigInteger> {
    val result = mutableListOf<BigInteger>()
    var i = ZERO

    while (i <= maxBit(number)) {
        if (testBit(number, i))
            result.add(i)

        i = i + ONE
    }

    return result
}

fun multiplyField(x: BigInteger, y: BigInteger): BigInteger {
    var result = ZERO
    var i = ZERO

    while (i <= maxBit(y)) {
        if (testBit(y, i)) {
            result = result.xor(x.shl(i))
        }

        i = i + ONE
    }

    return result
}

data class DivRes(val quotient: BigInteger, val reminder: BigInteger)

fun divideField(dividend: BigInteger, divider: BigInteger): DivRes {
    var reminder = dividend
    var quotient = ZERO

    while (maxBit(reminder) >= maxBit(divider)) {
        val diff = maxBit(reminder) - maxBit(divider)

        reminder = reminder.xor(divider.shl(diff))
        quotient = quotient.xor(ONE.shl(diff))
    }

    return DivRes(quotient, reminder)
}

class BCH(private val n: Int, private val dist: Int, private val primitivePolynomial: BigInteger) {
    val t: Int = (dist - 1) / 2
    private val m: BigInteger = maxBit(primitivePolynomial)
    private val minimalPolynomialClasses = mutableListOf<BigInteger>()
    private val fieldElementsToPolynomial: MutableMap<BigInteger, BigInteger>
    private val polynomialToFieldElements: MutableMap<BigInteger, BigInteger>
    var generatorPolynomial: BigInteger
    val k: Int

    init {
        // группируем минимальные многочлены по классам
        var polynomialsChecked = ONE
        val allPolynomials = pow2(pow2(m) - ONE) - ONE
        val polynomialClassesInField = mutableListOf<BigInteger>()
        var i = ZERO

        while (polynomialsChecked != allPolynomials) {
            polynomialClassesInField.add(ZERO)

            var k = ZERO

            while (true) {
                if (!testBit(polynomialsChecked, k))
                    break

                k = k + ONE
            }

            while (true) {
                if (testBit(polynomialClassesInField[i.toInt()], k))
                    break

                polynomialClassesInField[i.toInt()] = polynomialClassesInField[i.toInt()].xor(ONE.shl(k))
                k = (k * TWO) % (pow2(m) - ONE)
            }

            polynomialsChecked = polynomialsChecked.xor(polynomialClassesInField[i.toInt()])
            i = i + ONE
        }

        // выбираем только те, в которых лежат корни порождающего многочлена
        for (coset in polynomialClassesInField) {
            for (i in 1 until dist) {
                if (coset.testBit(i)) {
                    minimalPolynomialClasses.add(coset)
                    break
                }
            }
        }

        // строим таблицу выражений элементов поля через первых m(от 0 до m - 1) степеней примитивного многочлена
        fieldElementsToPolynomial = mutableMapOf(ONE.negate() to ZERO)
        i = ZERO

        // все степени до m - это они же сами
        while (i < m) {
            fieldElementsToPolynomial[i] = BigInteger.ONE.shl(i)
            i = i + ONE
        }
        // тк мы в поле 2^p - операция плюс равно операции минус
        // значит элемент м-ной степени выражается через 0..м-1 коэффиценты примитивного многочлена
        fieldElementsToPolynomial[m] = primitivePolynomial.and(pow2(m) - ONE)

        i = m + ONE
        while (i < pow2(m) - ONE) {
            // каждый следующий элемент - это умножаем предыдущий альфу ака двигаем все коэффиценты на 1
            // если у него появился элемент м-ной степени - выражаем его через предыдущие
            var newElement = fieldElementsToPolynomial[i - ONE]!!.shl(ONE)

            if (newElement.and(pow2(m)) != ZERO) {
                newElement = newElement.xor(fieldElementsToPolynomial[m]!!).and(pow2(m) - ONE)
            }

            fieldElementsToPolynomial[i] = newElement
            i = i + ONE
        }

        polynomialToFieldElements = fieldElementsToPolynomial.entries.associateBy({ it.value }) { it.key }.toMutableMap()

        // собственно порождающий многочлен - это наименьшее общее кратное всех минимальных многочленов его корней
        // тк M_{b}(x) = M_{b^p}(x) - то можно перемножить только по одному многочлену из каждого класса
        generatorPolynomial = createPolynomial(minimalPolynomialClasses[0])

        for (i in 1 until minimalPolynomialClasses.size) {
            generatorPolynomial =
                multiplyField(generatorPolynomial, createPolynomial(minimalPolynomialClasses[i]))
        }

        k = n - maxBit(generatorPolynomial).toInt()
    }

    fun encode(message: BigInteger): BigInteger {
        // систематическое кодирование бчх - сообщение возводим в степень, проверочные биты - остаток
        val power = maxBit(generatorPolynomial)
        val result = message.shl(power)

        return result.xor(divideField(dividend = result, divider = generatorPolynomial).reminder)
    }

    fun decode(receivedMessage2: BigInteger): BigInteger {
        var receivedMessage = receivedMessage2
        // y(x) = a(x)g(x) + e(x)
        // g(x) в корнях порождающего 0 - значит если какой-то синдром не 0 - есть ошибка
        val (syndromes, is_error) = calculateSyndromes(receivedMessage)

        if (is_error) {
            // ищем многочлен локаторов ошибок
            val (errorLocator, L) = berlekampMasseyDecode(syndromes)
            // находим его корни
            val roots = chienSearch(errorLocator, L)
            // корни в позиции
            val errorPositions = convertRootsToErrorPositions(roots, m)

            for (position in errorPositions) {
                receivedMessage = receivedMessage.xor(ONE.shl(position))
            }
        }

        return receivedMessage
    }


    private fun calculateSyndromes(receivedMessage: BigInteger): Pair<MutableList<BigInteger>, Boolean> {
        // это можно написать по-оптимальнее, но и так сойдет
        // тут используется метод герцеля из презентации
        // дополнительно смотрел https://dcn.icc.spbstu.ru/~petert/papers/PhD.pdf 37 страница
        // пояснение как работает
        // 1. принятое сообщение с(x) = y(x) + e(x) = p(x)*x^(n - k) + rem(x) + e(x) = a(x)g(x) + e(x)
        // где p(x) - информационный многочлен, rem(x) - остаток от деления на g(x), мы в gf2 - минус это плюс
        // тк g(x) - перемножение минимальный многочленов, то
        // 2. c(x) mod mai = e(x) mod mai
        // где mai - минимальный многочлен alpha^i, mai = x - alpha^i
        val syndromes = mutableListOf<BigInteger>()
        var isError = false

        for (i in 1 until dist) {
            var syndromePolynomial = receivedMessage

            for (coset in minimalPolynomialClasses) {
                if (coset.testBit(i)) {
                    // берем остаток на минимальный многочлен
                    syndromePolynomial =
                        divideField(syndromePolynomial, createPolynomial(coset)).reminder
                    break
                }
            }

            // подставляем alpha^i
            val length = maxBit(syndromePolynomial)
            var syndromePolynomialInAlpha = ZERO
            var j = ZERO

            while (j <= length) {
                if (testBit(syndromePolynomial, j)) {
                    syndromePolynomialInAlpha = syndromePolynomialInAlpha.or(ONE.shl(j * BigInteger.valueOf(i.toLong())))
                }

                j = j + ONE
            }

            // получили многочлен e(alpha^i) в коэффицентах от alpha - e2(alpha)
            // при этом тк primitivePolynomial(alhpa) = 0, то
            // e2(alpha) = primitivePolynomial(alpha) * quot(alpha) + rem(alpha) = rem(alpha)
            // поэтому возьмем остаток от примитивного многочлена
            if (maxBit(syndromePolynomialInAlpha) >= maxBit(primitivePolynomial)) {
                syndromePolynomialInAlpha = divideField(syndromePolynomialInAlpha, primitivePolynomial).reminder
            }

            // переведем полином синдрома в конкретный элемент поля
            val syndrome = polynomialToFieldElements[syndromePolynomialInAlpha]!!

            isError = isError || (syndrome != ONE.negate())
            syndromes.add(syndrome)
        }

        return syndromes to isError
    }

    fun createPolynomial(roots: BigInteger): BigInteger {
        // создаю полином по корням с помощью формул виета
        // https://ru.wikipedia.org/wiki/%D0%A4%D0%BE%D1%80%D0%BC%D1%83%D0%BB%D1%8B_%D0%92%D0%B8%D0%B5%D1%82%D0%B0
        if (roots == ZERO)
            return ZERO

        val numberOfFieldElements = BigInteger.valueOf(fieldElementsToPolynomial.size - 1L)
        val rootArray = bitIndices(number = roots)
        var result = ONE.shl(rootArray.size)

        for (i in 0 until rootArray.size) {
            var coefficient = ZERO

            for (subset in rootArray.getAllSubsets(i + 1)) {
                coefficient =
                    coefficient.xor(fieldElementsToPolynomial[subset.fold(ZERO) { l, r -> l + r } % numberOfFieldElements]!!)
            }

            val addition = coefficient.shl(rootArray.size - i - 1)

            result = result.xor(addition)
        }

        return result
    }

    private fun chienSearch(errorLocatorPolynomial: MutableList<BigInteger>, L: Int): MutableList<BigInteger> {
        val roots = mutableListOf<BigInteger>()

        for (candidate in 0 until pow2(m).toInt() - 1) {
            var result = fieldElementsToPolynomial[errorLocatorPolynomial[0]]!!

            for (polynomial_power in 1..L) {
                if (errorLocatorPolynomial[polynomial_power] >= ZERO) {
                    result = result.xor(
                        fieldElementsToPolynomial[(errorLocatorPolynomial[polynomial_power] + BigInteger.valueOf(candidate * polynomial_power.toLong()))
                                % (pow2(m) - ONE)]!!
                    )
                }
            }

            if (result == ZERO)
                roots.add(BigInteger.valueOf(candidate.toLong()))
        }

        return roots
    }

    private fun convertRootsToErrorPositions(roots: MutableList<BigInteger>, power: BigInteger): MutableList<BigInteger> {
        val positions = mutableListOf<BigInteger>()

        for (root in roots) {
            if (root == BigInteger.ZERO)
                positions.add(ZERO)
            else
                positions.add((pow2(power) - ONE - root))
        }

        return positions
    }

    private fun berlekampMasseyDecode(syndromes: MutableList<BigInteger>): Pair<MutableList<BigInteger>, Int> {
        val numberOfElements = pow2(m) - ONE
        var C = MutableList(2 * t) { ZERO }
        val B = MutableList(2 * t) { ZERO }
        var L = 0
        C[0] = ONE
        B[0] = ONE

        for (n in 0 until 2 * t) {
            var delta = ZERO

            for (i in 0 until L + 1) {
                if (!(C[i] != ZERO && fieldElementsToPolynomial[syndromes[n - i]]!! != ZERO)) {
                    continue
                }

                val ci = polynomialToFieldElements[C[i]]!!
                val si = syndromes[n - i]
                val elem = (ci + si) % numberOfElements

                delta = delta.xor(fieldElementsToPolynomial[elem]!!)
            }

            for (i in B.size - 1 downTo 0) {
                B[i] = if (i == 0) ZERO else B[i - 1]
            }

            if (delta != ZERO) {
                val T = MutableList(C.size) { i -> C[i] }

                for (i in 0 until C.size) {
                    val bi = polynomialToFieldElements[B[i]]!!
                    val di = polynomialToFieldElements[delta]!!

                    if (bi != ONE.negate()) {
                        val res = (bi + di) % numberOfElements
                        T[i] = T[i].xor(fieldElementsToPolynomial[res]!!)
                    }
                }

                if (2 * L <= n) {
                    for (i in 0 until C.size) {
                        B[i] = ZERO

                        val deltaIdx = numberOfElements - polynomialToFieldElements[delta]!!
                        val ci = polynomialToFieldElements[C[i]]!!

                        if (ci != ONE.negate()) {
                            val elem = (ci + deltaIdx) % numberOfElements

                            B[i] = fieldElementsToPolynomial[elem]!!
                        }
                    }

                    C = T
                    L = n + 1 - L
                } else {
                    C = T
                }
            }
        }

        val result = mutableListOf<BigInteger>()

        for (poly in C) {
            result.add(polynomialToFieldElements[poly]!!)
        }

        return result to L
    }
}

data class SimulationData(val probability: Double, val tries: Int, val errors: Int)

fun readInt() = readLine()!!.toInt()
fun readStrings() = readLine()!!.split(" ")
fun readInts() = readStrings().map { it.toInt() }
fun readDoubles() = readStrings().map { it.toDouble() }
fun readSimulation(input: List<String>): SimulationData {
    val (probS, triesS, errorsS) = input

    return SimulationData(probS.toDouble(), triesS.toInt(), errorsS.toInt())
}

const val shouldDebug = false

fun debugOutput(message: String, data: String) {
    if (shouldDebug) {
        System.err.println("DEBUG: $message")
        System.err.println(data)
    }
}

fun binaryForm(x: BigInteger): String {
    val result = StringBuilder()
    var current = x

    while (current != ZERO) {
        if (current % TWO == ONE)
            result.append("1")
        else
            result.append("0")

        current = current / TWO
    }

    return result.toString()
}

fun main() {
//    println(System.getProperty("user.dir"))
    System.setIn(FileInputStream("input.txt"))
    System.setOut(PrintStream("output.txt"))
//    System.setErr(PrintStream("err.txt"))

    val (n, prim, dist) = readInts()
    val bch = BCH(n, dist, BigInteger.valueOf(prim.toLong()))

    println(bch.k)
    println(binaryForm(bch.generatorPolynomial).toList().joinToString(separator = " "))

    while (System.`in`.available() != 0) {
        val input = readStrings()

        debugOutput("type", input[0])

        when (input[0]) {
            "Encode" -> {
                val inputVector = input.drop(1)

                var message = ZERO
                var base = ONE
                for (s in inputVector) {
                    if (s == "1") {
                        message = message + base
                    }
                    base = base * TWO
                }

                val encoded = bch.encode(message)

//                println(encoded)
                println(binaryForm(encoded).toMutableList().apply { addAll("0".repeat(n - size).toList()) }
                    .joinToString(separator = " "))
            }
            "Decode" -> {
                val inputVector = input.drop(1)

                var message = ZERO
                var base = ONE
                for (s in inputVector) {
                    if (s == "1") {
                        message = message + base
                    }
                    base = base * TWO
                }

                val decoded = bch.decode(message)

//                println(decoded)
                println(binaryForm(decoded).toMutableList().apply { addAll("0".repeat(n - size).toList()) }
                    .joinToString(separator = " "))
            }
            "Simulate" -> {
                val (prob, tries, errors) = readSimulation(input.drop(1))
                var currentErrors = 0

                for (currentTry in 1..tries) {
                    var errorsInWord = 0

                    for (j in 0 until n) {
                        if (Random.asJavaRandom().nextDouble() <= prob)
                            errorsInWord++
                    }

                    currentErrors += if (errorsInWord > bch.t) 1 else 0

                    if (currentErrors >= errors || currentTry == tries) {
                        println(currentErrors.toDouble() / currentTry)
                        break
                    }
                }
            }
            else -> {
                throw IllegalStateException("problems with input")
            }
        }
    }
}