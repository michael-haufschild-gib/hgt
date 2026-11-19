# Attaining the exact forced flow between least-prime branches

- **Stage** 1-in-progress
- **Target** On every large octave, cover the whole region \(V\) of least primes \(2X^{1/4}<p\le X^{5/16}\). Realize exactly its signed mass as positive endpoints paired outside \(V\), with all external partners of least prime \(2,3\), or \(5\).

In \(V\), each negative vertex is a triple and each positive vertex a semiprime. In a least-prime row \(p\), merge each negative triple \(pab\) to a different \(pz\) in the same row. The cube-root capacity on the sharp quotient \((X/p,2X/p]\) guarantees enough prime tails \(z\). The remaining semiprimes are exactly the positive excess, including when a row has no triples.

For each remaining \(pz\), split \(z\) into \(qr\) in the same quotient interval, with \(q\in\{2,3,5\}\). The prime number theorem on these windows and \(1/2+1/3+1/5>1\) give room for the entire prime row. Since \(5p^2<X\) uniformly, each target has ordered prime factors \(q<p<r\). Its middle prime recovers the row, its least prime distinguishes it from every internal target, and the injection within the row recovers the source. The signed total in \(V\) is therefore exactly the number of exported positive endpoints. This attains the universal cut lower bound with no unmatched point of \(V\). The signed mass has moved to explicitly identified small-prime branches; its cancellation against their other vertices remains a separate question.

For a narrow range of least-prime exponents \(t=\log p/\log X\in(1/4,1/3)\), the candidate fraction of the prime row left to export is \(1-\log((1-2t)/t)\), after the internal triples have been used. This predicts exactly which prescribed sets of small primes suffice for row-preserving export, away from equality. The endpoint case requires an error comparison in the sharp prime counts. [Forced least-prime flux](../3-formalized/rfc-signed-cube-root-boundary.md)
