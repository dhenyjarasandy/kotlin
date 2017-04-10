package inlinePropertyAccessors

fun main(args: Array<String>) {
    class A {
        val a: String
            inline get() {
                //Breakpoint!
                return System.nanoTime().toString()
            }
    }

    A().apply {
        a
    }
}

// RESUME: 1