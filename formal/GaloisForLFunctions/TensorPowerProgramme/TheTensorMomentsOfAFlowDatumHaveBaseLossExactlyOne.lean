import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The tensor moments of a flow datum have base loss exactly one

A **flow datum** over \`Spec ℤ\` has finitely many modes \`z_i\` with weights \`b_i\`; the Frobenius at
\`n\` acts on the mode \`i\` by \`n^{z_i}\`, so its trace is \`t(n) = Σ_i b_i n^{z_i}\`. With
\`z_i = ρ_i − ½\` this is a finite configuration of zeros, the motive \`⊕ ℤ(−ρ)\` of the tensor-power
trick over \`ℤ\`. All Frobenii are diagonal in one basis: the datum has no monodromy.

The \`k\`-th tensor moment \`D_k(σ) = Σ_n Λ(n) |t(n)|^{2k} n^{−σ}\` is the moment of the traces of
\`M^{⊗k} ⊗ M̄^{⊗k}\`. With the width \`W = max Re z_i\` over the modes of nonzero weight:

* **Coinvariants are everything** (\`ofReal_tsum_flowMomentTerm\`). For \`σ > 1 + 2kW\`,
  \`D_k(σ) = Σ_{a,a'} B_{a,a'} · (−ζ'/ζ)(σ − Z_{a,a'})\` over pairs of \`k\`-tuples of modes, with
  \`Z_{a,a'} = Σ z_{a_j} + Σ z̄_{a'_j}\` and \`B_{a,a'} = Π b_{a_j} Π b̄_{a'_j}\`: every tuple of modes
  contributes its own shifted copy of \`−ζ'/ζ\`.
* **Nothing cancels at the edge** (\`tendsto_sub_mul_flowMoment\`, \`edgeResidue_pos\`). As
  \`σ ↓ 1 + 2kW\`, \`(σ − 1 − 2kW) D_k(σ)\` tends to the edge residue
  \`Σ_w ‖Σ_{Σ z_a = w} Π b_a‖² > 0\`, the sum running over the top tuples (\`Re Σ z_a = kW\`): the
  tuples \`(a, a')\` with \`Z_{a,a'} = 2kW\` are exactly the conjugation pairs of top tuples.
* **Base loss exactly one** (\`summable_flowMomentTerm_iff\`). For distinct modes,
  \`D_k(σ) < ∞ ⇔ σ > 1 + 2kW\`, for every \`k\`.
* **The pole law is the conclusion** (\`exists_poleLaw_iff\`). A bound
  \`D_k(2kw₀ + A) < ∞\` for every \`k\` with \`A\` independent of \`k\` holds iff \`W ≤ w₀\`.

So the tensor-power trick over \`Spec ℤ\` without monodromy is a ruler with base loss exactly \`1\`:
the edge of every even tensor power is a conjugation pair of top modes, whose size is the unknown
width, and the poles of \`−ζ'/ζ\` at the shifted points \`1 + Z\` are not cancelled by anything.
-/

open Complex Filter Topology LSeries ArithmeticFunction
open scoped LSeries.notation ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

variable {ι : Type*} [Fintype ι]

/-- The trace of the flow datum with modes \`z\` and weights \`b\` at \`n\`: \`t(n) = Σ_i b_i n^{z_i}\`. -/
def flowTrace (z b : ι → ℂ) (n : ℕ) : ℂ := ∑ i, b i * (n : ℂ) ^ z i

/-- The terms \`Λ(n) |t(n)|^{2k} n^{−σ}\` of the \`k\`-th tensor moment. -/
def flowMomentTerm (z b : ι → ℂ) (k : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  Λ n * ‖flowTrace z b n‖ ^ (2 * k) * (n : ℝ) ^ (-σ)

/-! ### Convergence right of the edge -/

/-- \`Σ Λ(n) n^{−u}\` converges for real \`u > 1\`. -/
theorem summable_vonMangoldt_rpow {u : ℝ} (hu : 1 < u) :
    Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-u) := by
  have h := (LSeriesSummable_vonMangoldt (s := (u : ℂ)) (by simpa using hu)).norm
  refine h.congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [norm_term_eq, if_neg hn, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg
      vonMangoldt_nonneg, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem norm_natCast_cpow_le {n : ℕ} (hn : 1 ≤ n) {z : ℂ} {W : ℝ} (hz : z.re ≤ W) :
    ‖(n : ℂ) ^ z‖ ≤ (n : ℝ) ^ W := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hz

/-- The trace is at most \`(Σ ‖b_i‖) n^W\`. -/
theorem norm_flowTrace_le {z b : ι → ℂ} {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) {n : ℕ}
    (hn : 1 ≤ n) : ‖flowTrace z b n‖ ≤ (∑ i, ‖b i‖) * (n : ℝ) ^ W := by
  rw [flowTrace, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  by_cases hb : b i = 0
  · simp [hb]
  · exact mul_le_mul_of_nonneg_left (norm_natCast_cpow_le hn (hW i hb)) (norm_nonneg _)

theorem flowMomentTerm_nonneg (z b : ι → ℂ) (k : ℕ) (σ : ℝ) (n : ℕ) :
    0 ≤ flowMomentTerm z b k σ n :=
  mul_nonneg (mul_nonneg vonMangoldt_nonneg (pow_nonneg (norm_nonneg _) _))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Right of \`1 + 2kW\` the \`k\`-th tensor moment converges. -/
theorem summable_flowMomentTerm {z b : ι → ℂ} {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W)
    (k : ℕ) {σ : ℝ} (hσ : 1 + 2 * k * W < σ) : Summable (flowMomentTerm z b k σ) := by
  set B := ∑ i, ‖b i‖
  have hs := (summable_vonMangoldt_rpow (u := σ - 2 * k * W) (by linarith)).mul_left (B ^ (2 * k))
  refine Summable.of_nonneg_of_le (flowMomentTerm_nonneg z b k σ) (fun n => ?_) hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [flowMomentTerm]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ht := norm_flowTrace_le hW hn
  have hpow : ‖flowTrace z b n‖ ^ (2 * k) ≤ B ^ (2 * k) * (n : ℝ) ^ (2 * k * W) := by
    calc ‖flowTrace z b n‖ ^ (2 * k) ≤ (B * (n : ℝ) ^ W) ^ (2 * k) :=
          pow_le_pow_left₀ (norm_nonneg _) ht _
      _ = B ^ (2 * k) * (n : ℝ) ^ (2 * k * W) := by
          rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ W), ← Real.rpow_mul hn0.le]
          push_cast; ring_nf
  calc flowMomentTerm z b k σ n
      = Λ n * ‖flowTrace z b n‖ ^ (2 * k) * (n : ℝ) ^ (-σ) := rfl
    _ ≤ Λ n * (B ^ (2 * k) * (n : ℝ) ^ (2 * k * W)) * (n : ℝ) ^ (-σ) := by
        gcongr
    _ = B ^ (2 * k) * (Λ n * (n : ℝ) ^ (-(σ - 2 * k * W))) := by
        rw [show -(σ - 2 * k * W) = 2 * k * W + -σ by ring, Real.rpow_add hn0]
        ring

/-! ### Expansion over tuples of modes -/

section Expansion

variable (z b : ι → ℂ) {k : ℕ}

/-- The mode of a tuple: \`Σ_j z_{a_j}\`. -/
def tupleMode (a : Fin k → ι) : ℂ := ∑ j, z (a j)

/-- The weight of a tuple: \`Π_j b_{a_j}\`. -/
def tupleWeight (a : Fin k → ι) : ℂ := ∏ j, b (a j)

/-- The mode \`Z_{a,a'} = Σ z_{a_j} + Σ z̄_{a'_j}\` of a pair of tuples. -/
def pairMode (a a' : Fin k → ι) : ℂ := tupleMode z a + conj (tupleMode z a')

/-- The weight \`B_{a,a'} = Π b_{a_j} · Π b̄_{a'_j}\` of a pair of tuples. -/
def pairWeight (a a' : Fin k → ι) : ℂ := tupleWeight b a * conj (tupleWeight b a')

theorem natCast_cpow_sum {n : ℕ} (hn : n ≠ 0) (w : Fin k → ℂ) :
    (n : ℂ) ^ (∑ j, w j) = ∏ j, (n : ℂ) ^ w j := by
  have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [Complex.cpow_def_of_ne_zero h0, Finset.mul_sum, Complex.exp_sum]

theorem conj_natCast_cpow (n : ℕ) (w : ℂ) : conj ((n : ℂ) ^ w) = (n : ℂ) ^ conj w := by
  rcases eq_or_ne n 0 with rfl | hn
  · rcases eq_or_ne w 0 with rfl | hw
    · simp
    · rw [Nat.cast_zero, Complex.zero_cpow hw, Complex.zero_cpow ((map_ne_zero conj).mpr hw),
        map_zero]
  · have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_def_of_ne_zero h0, Complex.cpow_def_of_ne_zero h0, ← Complex.exp_conj,
      map_mul, Complex.natCast_log, Complex.conj_ofReal]

/-- \`t(n)^k = Σ_a (Π b_{a_j}) n^{Σ z_{a_j}}\`. -/
theorem flowTrace_pow {n : ℕ} (hn : n ≠ 0) :
    flowTrace z b n ^ k = ∑ a : Fin k → ι, tupleWeight b a * (n : ℂ) ^ tupleMode z a := by
  rw [flowTrace, ← Fin.prod_const, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_mul_distrib, tupleWeight, tupleMode, natCast_cpow_sum hn]

/-- \`|t(n)|^{2k} = Σ_{a,a'} B_{a,a'} n^{Z_{a,a'}}\`. -/
theorem ofReal_norm_flowTrace_pow {n : ℕ} (hn : n ≠ 0) :
    ((‖flowTrace z b n‖ ^ (2 * k) : ℝ) : ℂ) =
      ∑ p : (Fin k → ι) × (Fin k → ι), pairWeight b p.1 p.2 * (n : ℂ) ^ pairMode z p.1 p.2 := by
  have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsq : ((‖flowTrace z b n‖ ^ (2 * k) : ℝ) : ℂ) =
      flowTrace z b n ^ k * conj (flowTrace z b n ^ k) := by
    rw [pow_mul, Complex.ofReal_pow, Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq,
      ← Complex.mul_conj, mul_pow, map_pow]
  rw [hsq, flowTrace_pow z b hn, map_sum, Finset.sum_mul_sum, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [map_mul, conj_natCast_cpow, pairWeight, pairMode, Complex.cpow_add _ _ h0]
  ring

variable {z b}

theorem re_tupleMode_le {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) {a : Fin k → ι}
    (ha : tupleWeight b a ≠ 0) : (tupleMode z a).re ≤ k * W := by
  have hb : ∀ j, b (a j) ≠ 0 := fun j => (Finset.prod_ne_zero_iff.mp ha) j (Finset.mem_univ j)
  rw [tupleMode, Complex.re_sum]
  calc ∑ j, (z (a j)).re ≤ ∑ _j : Fin k, W := Finset.sum_le_sum fun j _ => hW _ (hb j)
    _ = k * W := by simp

theorem re_pairMode_le {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) {a a' : Fin k → ι}
    (h : pairWeight b a a' ≠ 0) : (pairMode z a a').re ≤ 2 * k * W := by
  have ha : tupleWeight b a ≠ 0 := left_ne_zero_of_mul h
  have ha' : tupleWeight b a' ≠ 0 := by
    have := right_ne_zero_of_mul h
    rwa [map_ne_zero] at this
  rw [pairMode, Complex.add_re, Complex.conj_re]
  linarith [re_tupleMode_le hW ha, re_tupleMode_le hW ha']

/-- **Coinvariants are everything.** Right of the edge the tensor moment is the sum over pairs of
tuples of modes of \`B_{a,a'} · L(Λ, σ − Z_{a,a'})\`. -/
theorem ofReal_tsum_flowMomentTerm_eq_sum_LSeries {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W)
    {σ : ℝ} (hσ : 1 + 2 * k * W < σ) :
    ((∑' n, flowMomentTerm z b k σ n : ℝ) : ℂ) =
      ∑ p : (Fin k → ι) × (Fin k → ι),
        pairWeight b p.1 p.2 * LSeries ↗Λ (σ - pairMode z p.1 p.2) := by
  have hsum : ∀ p : (Fin k → ι) × (Fin k → ι),
      Summable fun n => pairWeight b p.1 p.2 * term ↗Λ (σ - pairMode z p.1 p.2) n := by
    intro p
    by_cases h : pairWeight b p.1 p.2 = 0
    · simp [h]
    · refine (LSeriesSummable_vonMangoldt ?_).mul_left _
      rw [Complex.sub_re, Complex.ofReal_re]
      linarith [re_pairMode_le hW h]
  rw [Complex.ofReal_tsum]
  simp_rw [LSeries, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun p _ => hsum p]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [flowMomentTerm, term]
  have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [flowMomentTerm, Complex.ofReal_mul, Complex.ofReal_mul, ofReal_norm_flowTrace_pow z b hn,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [term_of_ne_zero hn, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast,
    Complex.ofReal_neg, Complex.cpow_neg, Complex.cpow_sub _ _ h0]
  field_simp

/-- The same identity with \`L(Λ, s) = −ζ'(s)/ζ(s)\`. -/
theorem ofReal_tsum_flowMomentTerm {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W)
    {σ : ℝ} (hσ : 1 + 2 * k * W < σ) :
    ((∑' n, flowMomentTerm z b k σ n : ℝ) : ℂ) =
      ∑ p : (Fin k → ι) × (Fin k → ι), pairWeight b p.1 p.2 *
        (-deriv riemannZeta (σ - pairMode z p.1 p.2) / riemannZeta (σ - pairMode z p.1 p.2)) := by
  rw [ofReal_tsum_flowMomentTerm_eq_sum_LSeries hW hσ]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : pairWeight b p.1 p.2 = 0
  · simp [h]
  · rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div]
    rw [Complex.sub_re, Complex.ofReal_re]
    linarith [re_pairMode_le hW h]

end Expansion

end GaloisForLFunctions.TensorPowerProgramme
