import GaloisForLFunctions.ArithmeticGaugeTheory.TheAdditivelyInvariantPoint
import GaloisForLFunctions.ArithmeticGaugeTheory.TheShellDecomposition

/-!
# The major arcs of the shells

The Haar average of the gauge-transformed prime pair form deletes every shell
(`integral_primePairForm_gaugeTransform`). A finite gauge subgroup deletes less. Averaging over the
gauge points of the Dirichlet characters of level `q` (`ArithmeticCorrelationGeometry.dirichletGauge`)
projects each pair `(km, n)` onto congruence: it survives exactly when `km ≡ n (mod q)`.

* **The level-`q` average** (`sum_primePairForm_dirichletGauge`). For weights and vectors supported
  on integers prime to `q`, the sum over characters mod `q` of the gauge-transformed form is `φ(q)`
  times the form restricted to the pairs with `km ≡ n (mod q)`.
* **Shells at level `q`** (`sum_shellPart_dirichletGauge`). In the shell part, a pair on the shell
  `n = km + j` survives the level-`q` average exactly when `q ∣ j`.
* **Ratio part** (`sum_ratioPart_dirichletGauge`). The ratio part is invariant at every level.

So the finite gauge subgroups see the shells through congruences: level `q` keeps the shells whose
shift is a multiple of `q`. These are the major arcs of the shell part. Haar measure, the limit of all
levels, keeps none of them. The singular series of a shell is the weighted count of the levels `q ∣ j`;
what lies beyond it is the discrepancy of the point `0`.
-/

open MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

variable {q : ℕ} [NeZero q] (K N : ℕ) (a x : ℕ → ℂ) (G : ℝ → ℂ)

/-- The character sum of one twist pair at level `q`, for arguments prime to `q`. -/
theorem sum_twistPair_dirichletGauge {k m n : ℕ} (hk : k ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hkq : Nat.Coprime k q) (hmq : Nat.Coprime m q) (hnq : Nat.Coprime n q) :
    ∑ χ : DirichletCharacter ℂ q,
        twist (dirichletGauge χ) (k * m) * conj (twist (dirichletGauge χ) n) =
      if ((k * m : ℕ) : ZMod q) = n then (q.totient : ℂ) else 0 :=
  sum_twist_dirichletGauge_mul_conj (Nat.mul_ne_zero hk hm) hn (Nat.Coprime.mul_left hkq hmq) hnq

/-- The level-`q` average of a combination of twist pairs, for coefficients supported on triples
prime to `q`. -/
theorem sum_twistPairCombination_dirichletGauge (c : ℕ → ℕ → ℕ → ℂ)
    (hc : ∀ k m n, c k m n ≠ 0 → Nat.Coprime k q ∧ Nat.Coprime m q ∧ Nat.Coprime n q) :
    ∑ χ : DirichletCharacter ℂ q, ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        c k m n * (twist (dirichletGauge χ) (k * m) * conj (twist (dirichletGauge χ) n)) =
      (q.totient : ℂ) * ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if ((k * m : ℕ) : ZMod q) = n then c k m n else 0 := by
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [← mul_sum]
  by_cases h0 : c k m n = 0
  · simp [h0]
  · obtain ⟨hkq, hmq, hnq⟩ := hc k m n h0
    rw [sum_twistPair_dirichletGauge (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1)
      (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hm).1) (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)
      hkq hmq hnq]
    split_ifs <;> ring

/-- Supports prime to `q`. -/
def CoprimeSupported (q : ℕ) (v : ℕ → ℂ) : Prop := ∀ n, v n ≠ 0 → Nat.Coprime n q

omit [NeZero q] in
theorem coprime_of_mul_ne_zero {a x : ℕ → ℂ} (ha : CoprimeSupported q a) (hx : CoprimeSupported q x)
    {k m n : ℕ} {c : ℂ} (h : a k * x m * conj (x n) * c ≠ 0) :
    Nat.Coprime k q ∧ Nat.Coprime m q ∧ Nat.Coprime n q := by
  have h1 : a k * x m * conj (x n) ≠ 0 := left_ne_zero_of_mul h
  have h2 : a k * x m ≠ 0 := left_ne_zero_of_mul h1
  refine ⟨ha k (left_ne_zero_of_mul h2), hx m (right_ne_zero_of_mul h2), hx n fun hn0 => ?_⟩
  exact (right_ne_zero_of_mul h1) (by rw [hn0, map_zero])

/-- **The level-`q` average of the prime pair form** keeps exactly the pairs with
`km ≡ n (mod q)`. -/
theorem sum_primePairForm_dirichletGauge (ha : CoprimeSupported q a) (hx : CoprimeSupported q x) :
    ∑ χ : DirichletCharacter ℂ q,
        primePairForm K N (gaugeTransform (dirichletGauge χ) a) (gaugeTransform (dirichletGauge χ) x) G =
      (q.totient : ℂ) * ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if ((k * m : ℕ) : ZMod q) = n then
          a k * x m * conj (x n) * G (Real.log n - Real.log m - Real.log k) else 0 := by
  have hexp : ∀ χ : DirichletCharacter ℂ q,
      primePairForm K N (gaugeTransform (dirichletGauge χ) a) (gaugeTransform (dirichletGauge χ) x) G =
        ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          a k * x m * conj (x n) * G (Real.log n - Real.log m - Real.log k) *
            (twist (dirichletGauge χ) (k * m) * conj (twist (dirichletGauge χ) n)) := by
    intro χ
    refine sum_congr rfl fun k hk => sum_congr rfl fun m hm => sum_congr rfl fun n _ => ?_
    exact shellTerm_gaugeTransform a x _ (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1)
      (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hm).1) n _
  simp_rw [hexp]
  exact sum_twistPairCombination_dirichletGauge K N _ fun k m n h =>
    coprime_of_mul_ne_zero ha hx h

/-- **Shells at level `q`.** In the shell part, the level-`q` average keeps the shell pairs with
`km ≡ n (mod q)` and deletes the others. -/
theorem sum_shellPart_dirichletGauge (ha : CoprimeSupported q a) (hx : CoprimeSupported q x) :
    ∑ χ : DirichletCharacter ℂ q,
        shellPart K N (gaugeTransform (dirichletGauge χ) a) (gaugeTransform (dirichletGauge χ) x) G =
      (q.totient : ℂ) * ∑ k ∈ Icc 1 K, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if ((k * m : ℕ) : ZMod q) = n then shellCoeff a x G k m n else 0 := by
  simp_rw [shellPart_gaugeTransform_eq]
  refine sum_twistPairCombination_dirichletGauge K N _ fun k m n h => ?_
  rw [shellCoeff] at h
  split_ifs at h with hn
  · exact absurd rfl h
  · exact coprime_of_mul_ne_zero ha hx h

omit [NeZero q] in
/-- A shell pair `n = km + j` survives the level-`q` average exactly when `q ∣ j`. -/
theorem shellPair_survives_iff {k m j : ℕ} :
    ((k * m : ℕ) : ZMod q) = ((k * m + j : ℕ) : ZMod q) ↔ q ∣ j := by
  rw [eq_comm, Nat.cast_add, add_eq_left, ZMod.natCast_eq_zero_iff]

omit [NeZero q] in
/-- **The ratio part is invariant at every level.** -/
theorem sum_ratioPart_dirichletGauge :
    ∑ χ : DirichletCharacter ℂ q,
        ratioPart K N (gaugeTransform (dirichletGauge χ) a) (gaugeTransform (dirichletGauge χ) x) G =
      (Fintype.card (DirichletCharacter ℂ q) : ℂ) * ratioPart K N a x G := by
  simp_rw [ratioPart_gaugeTransform]
  rw [sum_const, card_univ, nsmul_eq_mul]

end GaloisForLFunctions.ArithmeticGaugeTheory
