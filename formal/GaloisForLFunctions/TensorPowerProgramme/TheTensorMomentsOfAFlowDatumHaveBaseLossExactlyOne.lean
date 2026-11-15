import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The tensor moments of a flow datum have base loss exactly one

A **flow datum** over `Spec ℤ` has finitely many modes `z_i` with weights `b_i`; the Frobenius at
`n` acts on the mode `i` by `n^{z_i}`, so its trace is `t(n) = Σ_i b_i n^{z_i}`. With
`z_i = ρ_i − ½` this is a finite configuration of zeros, the motive `⊕ ℤ(−ρ)` of the tensor-power
trick over `ℤ`. All Frobenii are diagonal in one basis: the datum has no monodromy.

The `k`-th tensor moment `D_k(σ) = Σ_n Λ(n) |t(n)|^{2k} n^{−σ}` is the moment of the traces of
`M^{⊗k} ⊗ M̄^{⊗k}`. With the width `W = max Re z_i` over the modes of nonzero weight:

* **Coinvariants are everything** (`ofReal_tsum_flowMomentTerm`). For `σ > 1 + 2kW`,
  `D_k(σ) = Σ_{a,a'} B_{a,a'} · (−ζ'/ζ)(σ − Z_{a,a'})` over pairs of `k`-tuples of modes, with
  `Z_{a,a'} = Σ z_{a_j} + Σ z̄_{a'_j}` and `B_{a,a'} = Π b_{a_j} Π b̄_{a'_j}`: every tuple of modes
  contributes its own shifted copy of `−ζ'/ζ`.
* **Nothing cancels at the edge** (`tendsto_sub_mul_flowMoment`, `edgeResidue_pos`). As
  `σ ↓ 1 + 2kW`, `(σ − 1 − 2kW) D_k(σ)` tends to the edge residue
  `Σ_w ‖Σ_{Σ z_a = w} Π b_a‖² > 0`, the sum running over the top tuples (`Re Σ z_a = kW`): the
  tuples `(a, a')` with `Z_{a,a'} = 2kW` are exactly the conjugation pairs of top tuples.
* **Base loss exactly one** (`summable_flowMomentTerm_iff`). For distinct modes,
  `D_k(σ) < ∞ ⇔ σ > 1 + 2kW`, for every `k`.
* **The pole law is the conclusion** (`exists_poleLaw_iff`). A bound
  `D_k(2kw₀ + A) < ∞` for every `k` with `A` independent of `k` holds iff `W ≤ w₀`.

So the tensor-power trick over `Spec ℤ` without monodromy is a ruler with base loss exactly `1`:
the edge of every even tensor power is a conjugation pair of top modes, whose size is the unknown
width, and the poles of `−ζ'/ζ` at the shifted points `1 + Z` are not cancelled by anything.
-/

open Complex Filter Topology LSeries ArithmeticFunction
open scoped LSeries.notation ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

variable {ι : Type*} [Fintype ι]

/-- The trace of the flow datum with modes `z` and weights `b` at `n`: `t(n) = Σ_i b_i n^{z_i}`. -/
def flowTrace (z b : ι → ℂ) (n : ℕ) : ℂ := ∑ i, b i * (n : ℂ) ^ z i

/-- The terms `Λ(n) |t(n)|^{2k} n^{−σ}` of the `k`-th tensor moment. -/
def flowMomentTerm (z b : ι → ℂ) (k : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  Λ n * ‖flowTrace z b n‖ ^ (2 * k) * (n : ℝ) ^ (-σ)

/-! ### Convergence right of the edge -/

/-- `Σ Λ(n) n^{−u}` converges for real `u > 1`. -/
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

/-- The trace is at most `(Σ ‖b_i‖) n^W`. -/
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

/-- Right of `1 + 2kW` the `k`-th tensor moment converges. -/
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

/-- The mode of a tuple: `Σ_j z_{a_j}`. -/
def tupleMode (a : Fin k → ι) : ℂ := ∑ j, z (a j)

/-- The weight of a tuple: `Π_j b_{a_j}`. -/
def tupleWeight (a : Fin k → ι) : ℂ := ∏ j, b (a j)

/-- The mode `Z_{a,a'} = Σ z_{a_j} + Σ z̄_{a'_j}` of a pair of tuples. -/
def pairMode (a a' : Fin k → ι) : ℂ := tupleMode z a + conj (tupleMode z a')

/-- The weight `B_{a,a'} = Π b_{a_j} · Π b̄_{a'_j}` of a pair of tuples. -/
def pairWeight (a a' : Fin k → ι) : ℂ := tupleWeight b a * conj (tupleWeight b a')

theorem natCast_cpow_sum {n : ℕ} (hn : n ≠ 0) (w : Fin k → ℂ) :
    (n : ℂ) ^ (∑ j, w j) = ∏ j, (n : ℂ) ^ w j := by
  have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [Complex.cpow_def_of_ne_zero h0, Finset.mul_sum, Complex.exp_sum]

theorem conj_natCast_cpow (n : ℕ) (w : ℂ) : conj ((n : ℂ) ^ w) = (n : ℂ) ^ conj w := by
  rcases eq_or_ne n 0 with rfl | hn
  · rcases eq_or_ne w 0 with rfl | hw
    · simp
    · rw [Nat.cast_zero, Complex.zero_cpow hw, Complex.zero_cpow ((map_ne_zero conj).mpr hw)]
      simp
  · have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_def_of_ne_zero h0, Complex.cpow_def_of_ne_zero h0, ← Complex.exp_conj,
      map_mul, ← Complex.natCast_log, Complex.conj_ofReal]

/-- `t(n)^k = Σ_a (Π b_{a_j}) n^{Σ z_{a_j}}`. -/
theorem flowTrace_pow {n : ℕ} (hn : n ≠ 0) :
    flowTrace z b n ^ k = ∑ a : Fin k → ι, tupleWeight b a * (n : ℂ) ^ tupleMode z a := by
  rw [flowTrace, ← Fin.prod_const, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_mul_distrib, tupleWeight, tupleMode, natCast_cpow_sum hn]

/-- `|t(n)|^{2k} = Σ_{a,a'} B_{a,a'} n^{Z_{a,a'}}`. -/
theorem ofReal_norm_flowTrace_pow {n : ℕ} (hn : n ≠ 0) :
    ((‖flowTrace z b n‖ ^ (2 * k) : ℝ) : ℂ) =
      ∑ p : (Fin k → ι) × (Fin k → ι), pairWeight b p.1 p.2 * (n : ℂ) ^ pairMode z p.1 p.2 := by
  have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsq : ((‖flowTrace z b n‖ ^ (2 * k) : ℝ) : ℂ) =
      flowTrace z b n ^ k * conj (flowTrace z b n ^ k) := by
    have h2 : ((‖flowTrace z b n‖ ^ 2 : ℝ) : ℂ) = flowTrace z b n * conj (flowTrace z b n) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [pow_mul, Complex.ofReal_pow, h2, mul_pow, map_pow]
  rw [hsq, flowTrace_pow z b hn, map_sum, Finset.sum_mul_sum, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [map_mul, conj_natCast_cpow, pairWeight, pairMode, Complex.cpow_add _ _ h0]
  ring

variable {z b}

omit [Fintype ι] in
theorem re_tupleMode_le {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) {a : Fin k → ι}
    (ha : tupleWeight b a ≠ 0) : (tupleMode z a).re ≤ k * W := by
  have hb : ∀ j, b (a j) ≠ 0 := fun j => (Finset.prod_ne_zero_iff.mp ha) j (Finset.mem_univ j)
  rw [tupleMode, Complex.re_sum]
  calc ∑ j, (z (a j)).re ≤ ∑ _j : Fin k, W := Finset.sum_le_sum fun j _ => hW _ (hb j)
    _ = k * W := by simp

omit [Fintype ι] in
theorem re_pairMode_le {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) {a a' : Fin k → ι}
    (h : pairWeight b a a' ≠ 0) : (pairMode z a a').re ≤ 2 * k * W := by
  have ha : tupleWeight b a ≠ 0 := left_ne_zero_of_mul h
  have ha' : tupleWeight b a' ≠ 0 := by
    have := right_ne_zero_of_mul h
    rwa [map_ne_zero] at this
  rw [pairMode, Complex.add_re, Complex.conj_re]
  linarith [re_tupleMode_le hW ha, re_tupleMode_le hW ha']

/-- **Coinvariants are everything.** Right of the edge the tensor moment is the sum over pairs of
tuples of modes of `B_{a,a'} · L(Λ, σ − Z_{a,a'})`. -/
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

/-- The same identity with `L(Λ, s) = −ζ'(s)/ζ(s)`. -/
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

/-! ### The edge: a pole of positive residue -/

section Edge

/-- `L(Λ, s) − 1/(s − 1)`, continued to `Re s ≥ 1` (the residue-class function for `q = 1`). -/
def vonMangoldtRegular : ℂ → ℂ :=
  ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (q := 1) (1 : ZMod 1)

theorem continuousOn_vonMangoldtRegular : ContinuousOn vonMangoldtRegular {s | 1 ≤ s.re} :=
  ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux _

theorem LSeries_vonMangoldt_eq_regular_add {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗Λ s = vonMangoldtRegular s + 1 / (s - 1) := by
  have h := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) (a := 1)
    isUnit_one (Set.mem_setOf.mpr hs)
  have hrc : ArithmeticFunction.vonMangoldt.residueClass (q := 1) 1 = fun n => Λ n := by
    funext n
    simp only [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply,
      Set.mem_setOf_eq]
    rw [if_pos (Subsingleton.elim _ _)]
  rw [vonMangoldtRegular, h]
  simp only [hrc, Nat.totient_one, Nat.cast_one, inv_one]
  ring

/-- `x − e → 0` as `x ↓ e`. -/
theorem tendsto_sub_nhdsGT (e : ℝ) : Tendsto (fun x : ℝ => x - e) (𝓝[>] e) (𝓝 0) := by
  have h := ((continuous_sub_right e).tendsto e).mono_left (nhdsWithin_le_nhds (s := Set.Ioi e))
  rwa [sub_self] at h

/-- Near the edge `e` the shifted copy `L(Λ, x − Z)` with `Re Z ≤ e − 1`, multiplied by
`x − e`, tends to `1` if `Z = e − 1` and to `0` otherwise. -/
theorem tendsto_sub_mul_LSeries_vonMangoldt {e : ℝ} {Z : ℂ} (hZ : Z.re ≤ e - 1) :
    Tendsto (fun x : ℝ => ((x - e : ℝ) : ℂ) * LSeries ↗Λ (x - Z)) (𝓝[>] e)
      (𝓝 (if Z = ((e - 1 : ℝ) : ℂ) then 1 else 0)) := by
  have hev : ∀ᶠ x : ℝ in 𝓝[>] e, ((x - e : ℝ) : ℂ) * LSeries ↗Λ (x - Z) =
      ((x - e : ℝ) : ℂ) * vonMangoldtRegular (x - Z) +
        ((x - e : ℝ) : ℂ) / (((x - e : ℝ) : ℂ) + (((e - 1 : ℝ) : ℂ) - Z)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : 1 < ((x : ℂ) - Z).re := by
      rw [Complex.sub_re, Complex.ofReal_re]; linarith [Set.mem_Ioi.mp hx]
    rw [LSeries_vonMangoldt_eq_regular_add hx', mul_add]
    congr 1
    rw [mul_one_div]
    congr 1
    push_cast; ring
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have h0 : Tendsto (fun x : ℝ => ((x - e : ℝ) : ℂ)) (𝓝[>] e) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_sub_nhdsGT e)
    rw [Complex.ofReal_zero] at h
    exact h
  have hreg : Tendsto (fun x : ℝ => vonMangoldtRegular (x - Z)) (𝓝[>] e)
      (𝓝 (vonMangoldtRegular ((e : ℂ) - Z))) := by
    have hmem : ((e : ℂ) - Z) ∈ {s : ℂ | 1 ≤ s.re} := by
      simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.ofReal_re]; linarith
    have hcw := continuousOn_vonMangoldtRegular ((e : ℂ) - Z) hmem
    refine hcw.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
    · have : Tendsto (fun x : ℝ => (x : ℂ) - Z) (𝓝 e) (𝓝 ((e : ℂ) - Z)) :=
        ((Complex.continuous_ofReal.sub continuous_const).tendsto e)
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [Set.mem_Ioi.mp hx]
  have h1 := h0.mul hreg
  rw [zero_mul] at h1
  by_cases hZe : Z = ((e - 1 : ℝ) : ℂ)
  · rw [if_pos hZe]
    have h2 : ∀ᶠ x : ℝ in 𝓝[>] e,
        ((x - e : ℝ) : ℂ) / (((x - e : ℝ) : ℂ) + (((e - 1 : ℝ) : ℂ) - Z)) = 1 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hne : ((x - e : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (sub_pos.mpr (Set.mem_Ioi.mp hx)).ne'
      rw [hZe, sub_self, add_zero, div_self hne]
    simpa using h1.add (tendsto_const_nhds.congr' (EventuallyEq.symm h2))
  · rw [if_neg hZe]
    have hd : ((e - 1 : ℝ) : ℂ) - Z ≠ 0 := sub_ne_zero.mpr (Ne.symm hZe)
    have h2 : Tendsto (fun x : ℝ => ((x - e : ℝ) : ℂ) / (((x - e : ℝ) : ℂ) +
        (((e - 1 : ℝ) : ℂ) - Z))) (𝓝[>] e) (𝓝 0) := by
      have := h0.div (h0.add_const (((e - 1 : ℝ) : ℂ) - Z)) (by rwa [zero_add])
      rw [zero_add, zero_div] at this
      exact this
    simpa using h1.add h2

variable {z b : ι → ℂ} {k : ℕ}

/-- The **edge residue**: the total weight of the pairs of tuples whose mode is the edge `2kW`. -/
def edgeResidue (z b : ι → ℂ) (k : ℕ) (W : ℝ) : ℂ :=
  ∑ p : (Fin k → ι) × (Fin k → ι),
    if pairMode z p.1 p.2 = ((2 * k * W : ℝ) : ℂ) then pairWeight b p.1 p.2 else 0

/-- `(σ − 1 − 2kW) D_k(σ)` tends to the edge residue as `σ ↓ 1 + 2kW`. -/
theorem tendsto_sub_mul_flowMoment {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) :
    Tendsto (fun x : ℝ => (((x - (1 + 2 * k * W)) * ∑' n, flowMomentTerm z b k x n : ℝ) : ℂ))
      (𝓝[>] (1 + 2 * k * W)) (𝓝 (edgeResidue z b k W)) := by
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (1 + 2 * k * W),
      ∑ p : (Fin k → ι) × (Fin k → ι), pairWeight b p.1 p.2 *
        (((x - (1 + 2 * k * W) : ℝ) : ℂ) * LSeries ↗Λ (x - pairMode z p.1 p.2)) =
      (((x - (1 + 2 * k * W)) * ∑' n, flowMomentTerm z b k x n : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Complex.ofReal_mul, ofReal_tsum_flowMomentTerm_eq_sum_LSeries hW (Set.mem_Ioi.mp hx),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  refine Tendsto.congr' hev (tendsto_finsetSum _ fun p _ => ?_)
  by_cases hp : pairWeight b p.1 p.2 = 0
  · simp only [hp, zero_mul, ite_self]
    exact tendsto_const_nhds
  · have hZ : (pairMode z p.1 p.2).re ≤ (1 + 2 * k * W) - 1 := by
      linarith [re_pairMode_le hW hp]
    have h := (tendsto_sub_mul_LSeries_vonMangoldt hZ).const_mul (pairWeight b p.1 p.2)
    have he : (1 + 2 * k * W) - 1 = 2 * k * W := by ring
    rw [he] at h
    convert h using 2
    split_ifs <;> simp

/-! ### The edge residue is a sum of squares -/

/-- The weight of all tuples of mode `u`. -/
def modeWeight (z b : ι → ℂ) (k : ℕ) (u : ℂ) : ℂ :=
  ∑ a : Fin k → ι, if tupleMode z a = u then tupleWeight b a else 0

omit [Fintype ι] in
theorem pairMode_eq_iff {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) {a a' : Fin k → ι}
    (h : pairWeight b a a' ≠ 0) :
    pairMode z a a' = ((2 * k * W : ℝ) : ℂ) ↔
      tupleMode z a = tupleMode z a' ∧ (tupleMode z a).re = k * W := by
  have ha : tupleWeight b a ≠ 0 := left_ne_zero_of_mul h
  have ha' : tupleWeight b a' ≠ 0 := by
    have := right_ne_zero_of_mul h
    rwa [map_ne_zero] at this
  have h1 := re_tupleMode_le hW ha
  have h2 := re_tupleMode_le hW ha'
  rw [pairMode, Complex.ext_iff, Complex.ext_iff]
  simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re, Complex.add_im, Complex.conj_im,
    Complex.ofReal_im]
  constructor
  · rintro ⟨hre, him⟩
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · rintro ⟨⟨hre, him⟩, htop⟩
    refine ⟨by linarith, by linarith⟩

/-- **The edge residue is a sum of squares** over the modes of top tuples. -/
theorem edgeResidue_eq_sum_normSq {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) :
    edgeResidue z b k W = ∑ u ∈ (Finset.univ.filter fun a : Fin k → ι =>
        (tupleMode z a).re = k * W).image (tupleMode z),
      ((‖modeWeight z b k u‖ ^ 2 : ℝ) : ℂ) := by
  classical
  set T := Finset.univ.filter fun a : Fin k → ι => (tupleMode z a).re = k * W
  -- a pair lies on the edge iff its tuples have the same top mode
  have hterm : ∀ p : (Fin k → ι) × (Fin k → ι),
      (if pairMode z p.1 p.2 = ((2 * k * W : ℝ) : ℂ) then pairWeight b p.1 p.2 else 0) =
        if p.1 ∈ T ∧ tupleMode z p.2 = tupleMode z p.1 then pairWeight b p.1 p.2 else 0 := by
    intro p
    by_cases hp : pairWeight b p.1 p.2 = 0
    · simp [hp]
    · have := pairMode_eq_iff hW hp
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h1 : pairMode z p.1 p.2 = ((2 * k * W : ℝ) : ℂ)
      · rw [if_pos h1, if_pos ⟨(this.mp h1).2, (this.mp h1).1.symm⟩]
      · rw [if_neg h1, if_neg fun h2 => h1 (this.mpr ⟨h2.2.symm, h2.1⟩)]
  rw [edgeResidue, Finset.sum_congr rfl fun p _ => hterm p, ← Finset.univ_product_univ,
    Finset.sum_product]
  -- sum over the second tuple first
  have hinner : ∀ a : Fin k → ι, (∑ a' : Fin k → ι,
      if a ∈ T ∧ tupleMode z a' = tupleMode z a then pairWeight b a a' else 0) =
      if a ∈ T then tupleWeight b a * conj (modeWeight z b k (tupleMode z a)) else 0 := by
    intro a
    by_cases ha : a ∈ T
    · simp only [ha, true_and, if_true, modeWeight, map_sum, Finset.mul_sum, pairWeight]
      refine Finset.sum_congr rfl fun a' _ => ?_
      split_ifs <;> simp
    · simp [ha]
  rw [Finset.sum_congr rfl fun a _ => hinner a, ← Finset.sum_filter,
    show (Finset.univ.filter fun a : Fin k → ι => a ∈ T) = T by ext a; simp]
  rw [← Finset.sum_fiberwise_of_maps_to (g := tupleMode z) (t := T.image (tupleMode z))
    (fun a ha => Finset.mem_image_of_mem _ ha)]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp hu
  -- the fibre of the mode of a top tuple consists of top tuples
  have hfil : (T.filter fun a => tupleMode z a = tupleMode z a₀) =
      Finset.univ.filter fun a => tupleMode z a = tupleMode z a₀ := by
    ext a
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      exact (Finset.mem_filter.mp ha₀).2
  rw [Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2], ← Finset.sum_mul, hfil,
    Finset.sum_filter, ← modeWeight, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_pow]

/-- **Nothing cancels at the edge.** For distinct modes the edge residue is real and at least
`‖b_{i*}‖^{2k} > 0`, where `i*` is the top mode of largest imaginary part. -/
theorem edgeResidue_pos {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W)
    (hWa : ∃ i, b i ≠ 0 ∧ (z i).re = W)
    (hinj : ∀ i j, b i ≠ 0 → b j ≠ 0 → z i = z j → i = j) :
    ∃ r : ℝ, 0 < r ∧ edgeResidue z b k W = r := by
  classical
  set Top := Finset.univ.filter fun i => b i ≠ 0 ∧ (z i).re = W
  obtain ⟨i₀, hi₀⟩ := hWa
  have hTop : Top.Nonempty := ⟨i₀, by simp [Top, hi₀.1, hi₀.2]⟩
  obtain ⟨is, his, hmax⟩ := Finset.exists_max_image Top (fun i => (z i).im) hTop
  have his' : b is ≠ 0 ∧ (z is).re = W := by simpa [Top] using his
  set c : Fin k → ι := fun _ => is
  -- the only tuple of nonzero weight with the mode of the constant tuple is the constant tuple
  have hconst : ∀ a : Fin k → ι, tupleMode z a = tupleMode z c → tupleWeight b a ≠ 0 → a = c := by
    intro a hv hw
    have hb : ∀ j, b (a j) ≠ 0 := fun j => (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
    have hre : ∀ j, (z (a j)).re = W := by
      have h1 : ∑ j, (z (a j)).re = ∑ _j : Fin k, W := by
        have := congrArg Complex.re hv
        simp only [tupleMode, Complex.re_sum, c, his'.2] at this
        simpa using this
      exact fun j => (Finset.sum_eq_sum_iff_of_le fun j _ => hW _ (hb j)).mp h1 j
        (Finset.mem_univ j)
    have him : ∀ j, (z (a j)).im = (z is).im := by
      have hle : ∀ j ∈ Finset.univ, (z (a j)).im ≤ (z is).im := fun j _ =>
        hmax _ (by simp [Top, hb j, hre j])
      have h1 : ∑ j, (z (a j)).im = ∑ _j : Fin k, (z is).im := by
        have := congrArg Complex.im hv
        simpa [tupleMode, Complex.im_sum, c] using this
      exact fun j => (Finset.sum_eq_sum_iff_of_le hle).mp h1 j (Finset.mem_univ j)
    funext j
    exact hinj _ _ (hb j) his'.1 (Complex.ext (by rw [hre j, his'.2]) (him j))
  have hmw : modeWeight z b k (tupleMode z c) = b is ^ k := by
    rw [modeWeight, Finset.sum_eq_single c]
    · simp [c, tupleWeight]
    · intro a _ hac
      split_ifs with hv
      · by_contra hw
        exact hac (hconst a hv hw)
      · rfl
    · simp
  have hcT : c ∈ Finset.univ.filter fun a : Fin k → ι => (tupleMode z a).re = k * W := by
    simp [c, tupleMode, his'.2]
  refine ⟨∑ u ∈ (Finset.univ.filter fun a : Fin k → ι => (tupleMode z a).re = k * W).image
      (tupleMode z), ‖modeWeight z b k u‖ ^ 2, ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun u _ => sq_nonneg ‖modeWeight z b k u‖)
      (Finset.mem_image_of_mem _ hcT))
    rw [hmw]
    exact pow_pos (norm_pos_iff.mpr (pow_ne_zero _ his'.1)) 2
  · rw [edgeResidue_eq_sum_normSq hW, Complex.ofReal_sum]

/-! ### Base loss exactly one -/

/-- **Base loss exactly one.** For a flow datum with distinct modes and width `W`, the `k`-th
tensor moment converges exactly right of `1 + 2kW`. -/
theorem summable_flowMomentTerm_iff {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W)
    (hWa : ∃ i, b i ≠ 0 ∧ (z i).re = W)
    (hinj : ∀ i j, b i ≠ 0 → b j ≠ 0 → z i = z j → i = j) (k : ℕ) (σ : ℝ) :
    Summable (flowMomentTerm z b k σ) ↔ 1 + 2 * k * W < σ := by
  refine ⟨fun hs => ?_, summable_flowMomentTerm hW k⟩
  by_contra hσ
  push Not at hσ
  set e := 1 + 2 * k * W
  obtain ⟨r, hr, hres⟩ := edgeResidue_pos (k := k) hW hWa hinj
  set M := ∑' n, flowMomentTerm z b k σ n
  -- right of the edge the moment is at most its value at σ
  have hbound : ∀ x : ℝ, e < x → ∑' n, flowMomentTerm z b k x n ≤ M := by
    intro x hx
    have hle : ∀ n, flowMomentTerm z b k x n ≤ flowMomentTerm z b k σ n := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [flowMomentTerm]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg vonMangoldt_nonneg
        (pow_nonneg (norm_nonneg _) _))
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
    exact Summable.tsum_le_tsum hle (summable_flowMomentTerm hW k hx) hs
  have hlim := tendsto_sub_mul_flowMoment (k := k) hW
  rw [hres] at hlim
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  have hup : Tendsto (fun x : ℝ => (x - e) * M) (𝓝[>] e) (𝓝 0) := by
    have h := (tendsto_sub_nhdsGT e).mul_const M
    rwa [zero_mul] at h
  have hle : ∀ᶠ x : ℝ in 𝓝[>] e, (x - e) * ∑' n, flowMomentTerm z b k x n ≤ (x - e) * M := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_le_mul_of_nonneg_left (hbound x hx) (sub_pos.mpr hx).le
  have := le_of_tendsto_of_tendsto hre hup hle
  linarith

/-- **The pole law is the conclusion.** For a flow datum, a bound `D_k(2kw₀ + A) < ∞` for every
`k`, with `A` independent of `k`, holds iff the width is at most `w₀`. -/
theorem exists_poleLaw_iff {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W)
    (hWa : ∃ i, b i ≠ 0 ∧ (z i).re = W)
    (hinj : ∀ i j, b i ≠ 0 → b j ≠ 0 → z i = z j → i = j) (w₀ : ℝ) :
    (∃ A : ℝ, ∀ k : ℕ, Summable (flowMomentTerm z b k (2 * k * w₀ + A))) ↔ W ≤ w₀ := by
  constructor
  · rintro ⟨A, hA⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := exists_nat_gt ((A - 1) / (2 * (W - w₀)))
    have h := (summable_flowMomentTerm_iff hW hWa hinj k _).mp (hA k)
    rw [div_lt_iff₀ (by linarith)] at hk
    nlinarith
  · intro hle
    refine ⟨2, fun k => summable_flowMomentTerm hW k ?_⟩
    have : (2 * k * W : ℝ) ≤ 2 * k * w₀ :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    linarith

end Edge

end GaloisForLFunctions.TensorPowerProgramme
