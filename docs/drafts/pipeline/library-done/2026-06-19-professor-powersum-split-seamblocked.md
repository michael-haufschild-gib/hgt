# Library note — 2026-06-19 (Professor): the power-sum arch/prime split is SEAM-BLOCKED (use explicit-formula B-L λ_n^∞)

**For:** librarian — flag in bucket-the-no-margin / bucket-the-seam-archimedean-obstruction and the
finite-free-convolution-flow / erosion-threshold / Keiper-Li narratives (prevents re-chasing; tried by DeWitt ×2,
Wheeler ×1).

**Finding (computed, dps=120).** The arch/prime split of the POWER SUMS (`P_k=Σρ^{−k}` or `σ_k=Σ(¼+γ²)^{−k}`)
does NOT give a usable `λ_n^arch` subtraction: `λ_n^arch = −Σ binom(n,j)(−1)^j P_j^arch` with
`P_j^arch=1−(−1)^jζ(j)/2^j` **blows up ~1.5^n** (3453 → 4e17 for n=20→100). λ_n^arch and λ_n^prime are each
exponentially large and cancel to the polynomial full λ_n. **Seam-blocked** (DeWitt's diagnosis, verified).

**Mechanism.** `|1−1/ρ|=1` exactly on the critical line (`|1−1/ρ|²=((γ²−¼)²+γ²)/(¼+γ²)²=1`), so the Li terms
`1−(1−1/ρ)^n` are bounded (on the unit circle) ⟹ full λ_n polynomial. The power-sum split expands
`(1−1/ρ)^n` OFF that unit-circle structure ⟹ each piece ~1.5^n ⟹ catastrophic cancellation. (Also: RH ⟺
|1−1/ρ|=1 ∀ρ, Li geometry.)

**The usable handle.** The clean archimedean/prime split is the **explicit-formula Bombieri–Lagarias**
`λ_n = λ_n^∞ (archimedean integral, polynomial) + λ_n^zeros (bounded)`, computed DIRECTLY from the explicit
formula — NOT from the power-sum P_j binomial transform. (Correction: an earlier "λ_n^arch ~ ½ n log n" was the
B-L λ_n^∞, conflated with the power-sum split; the power-sum route cannot yield the B-L coefficient.) DeWitt is
verifying the λ_n^∞ coefficient directly; Wheeler's linear-Li route should use λ_n^∞, not σ_k^arch.
