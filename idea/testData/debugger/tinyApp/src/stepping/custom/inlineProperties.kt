package inlineProperties

fun main(args: Array<String>) {
    class A {
        inline val a: String
            get() {
                //Breakpoint!
                return System.nanoTime().toString()
            }
    }

    A().apply {
        a
    }
}

// RESUME: 1