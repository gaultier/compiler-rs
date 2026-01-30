package main

func main() {
	var i = 0

	var a = 0
	var b = 1

	for {
		var tmp = b
		b = a + b
		a = tmp

		println(b)

		i = i + 1

		if i == 10 {
			break
		}
	}
}
