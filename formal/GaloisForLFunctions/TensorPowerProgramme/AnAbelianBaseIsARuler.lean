import GaloisForLFunctions.TensorPowerProgramme.TheTensorMomentsOfAFlowDatumHaveBaseLossExactlyOne

/-!
# An abelian base is a ruler

An **abelian base** (`IsAbelianBase`) has points `x` with norms `N(x) ≥ 1` and von Mangoldt
weights `λ(x) ≥ 0`, and a commutative group `C` of characters evaluated at the points:
multiplicative, of size at most one, with conjugation acting as inversion, linearly independent as
functions. Its analytic package is the prime number theorem of each character:
`F_ψ(s) = Σ_x λ(x) ψ(x) N(x)^{−s}` is, on `Re s > 1`, a function continuous on `Re s ≥ 1` plus
`[ψ = 1]/(s − 1)`. Dirichlet characters over `Spec ℤ` form one (`isAbelianBase_dirichlet`).

A twisted flow datum on the base has trace `t(x) = Σ_i b_i χ_i(x) N(x)^{z_i}`; every local system is
a sum of characters, so its monodromy is abelian. With `W = max Re z_i` over the modes of nonzero
weight and distinct pairs `(z_i, χ_i)`:

* **Coinvariants** (`ofReal_tsum_twistMomentTerm_eq_sum`). For `σ > 1 + 2kW` the `k`-th tensor
  moment `D_k(σ) = Σ_x λ(x) |t(x)|^{2k} N(x)^{−σ}` is `Σ_{a,a'} B_{a,a'} F_{χ_a χ_{a'}⁻¹}(σ − Z_{a,a'})`
  over pairs of `k`-tuples of modes.
* **The edge is a conjugation pair** (`tendsto_sub_mul_twistMoment`, `twistEdgeResidue_pos`). Only
  pairs with `Z_{a,a'} = 2kW` and `χ_a = χ_{a'}` reach the edge: the conjugation pairs of top
  tuples with equal mode and character. The residue is `Σ ‖Σ_{(Σ z_a, χ_a) = κ} Π b_a‖² > 0`;
  positivity is the linear independence of the characters.
* **Base loss exactly one** (`summable_twistMomentTerm_iff`): `D_k(σ) < ∞ ⇔ σ > 1 + 2kW` for
  `k ≥ 1`; and **the pole law is the conclusion** (`exists_twistPoleLaw_iff`).
* **Dirichlet twists** (`summable_dirichletMomentTerm_iff`): the same law over `Spec ℤ` for data
  twisted by Dirichlet characters of any modulus.

So abelian monodromy gains nothing: the edge of every even tensor power is a conjugation pair, whose
size is the unknown width. The family of twists, a candidate base for a pencil through `ζ`, is a
ruler.
-/

open Complex Filter Topology LSeries ArithmeticFunction
open scoped LSeries.notation ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

/-- The series `Σ_x λ(x) ψ(x) N(x)^{−s}` of the prime number theorem of the character `ψ`. -/
def baseLSeries {P C : Type*} (N lam : P → ℝ) (ev : C → P → ℂ) (ψ : C) (s : ℂ) : ℂ :=
  ∑' x, (lam x : ℂ) * ev ψ x * (N x : ℂ) ^ (-s)

/-- An **abelian base**: points with norms `N ≥ 1` and weights `λ ≥ 0`, characters `ev ψ` at the
points, and the prime number theorem of every character. -/
structure IsAbelianBase {P C : Type*} [CommGroup C] (N lam : P → ℝ) (ev : C → P → ℂ) : Prop where
  one_le_norm : ∀ x, 1 ≤ N x
  lam_nonneg : ∀ x, 0 ≤ lam x
  summable_lam : ∀ σ : ℝ, 1 < σ → Summable fun x => lam x * N x ^ (-σ)
  norm_ev_le : ∀ ψ x, ‖ev ψ x‖ ≤ 1
  ev_mul : ∀ ψ ψ' x, ev (ψ * ψ') x = ev ψ x * ev ψ' x
  conj_ev : ∀ ψ x, conj (ev ψ x) = ev ψ⁻¹ x
  pnt_one : ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
    baseLSeries N lam ev 1 s = G s + 1 / (s - 1)
  pnt_ne : ∀ ψ, ψ ≠ 1 → ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
    baseLSeries N lam ev ψ s = G s
  indep : LinearIndependent ℂ ev

variable {P C ι : Type*} [CommGroup C] [Fintype ι] {N lam : P → ℝ} {ev : C → P → ℂ}

/-- The trace of the twisted flow datum: `t(x) = Σ_i b_i χ_i(x) N(x)^{z_i}`. -/
def twistTrace (N : P → ℝ) (ev : C → P → ℂ) (z b : ι → ℂ) (χ : ι → C) (x : P) : ℂ :=
  ∑ i, b i * ev (χ i) x * (N x : ℂ) ^ z i

/-- The terms `λ(x) |t(x)|^{2k} N(x)^{−σ}` of the `k`-th tensor moment. -/
def twistMomentTerm (N lam : P → ℝ) (ev : C → P → ℂ) (z b : ι → ℂ) (χ : ι → C) (k : ℕ) (σ : ℝ)
    (x : P) : ℝ :=
  lam x * ‖twistTrace N ev z b χ x‖ ^ (2 * k) * N x ^ (-σ)

theorem norm_ofReal_cpow_le {r : ℝ} (hr : 1 ≤ r) {w : ℂ} {W : ℝ} (hw : w.re ≤ W) :
    ‖(r : ℂ) ^ w‖ ≤ r ^ W := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hr hw

theorem norm_twistTrace_le (hB : IsAbelianBase N lam ev) {z b : ι → ℂ} (χ : ι → C) {W : ℝ}
    (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) (x : P) :
    ‖twistTrace N ev z b χ x‖ ≤ (∑ i, ‖b i‖) * N x ^ W := by
  rw [twistTrace, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul]
  by_cases hb : b i = 0
  · simp [hb]
  · calc ‖b i‖ * ‖ev (χ i) x‖ * ‖(N x : ℂ) ^ z i‖ ≤ ‖b i‖ * 1 * N x ^ W := by
          gcongr
          · exact hB.norm_ev_le _ _
          · exact norm_ofReal_cpow_le (hB.one_le_norm x) (hW i hb)
      _ = ‖b i‖ * N x ^ W := by ring

theorem twistMomentTerm_nonneg (hB : IsAbelianBase N lam ev) (z b : ι → ℂ) (χ : ι → C) (k : ℕ)
    (σ : ℝ) (x : P) : 0 ≤ twistMomentTerm N lam ev z b χ k σ x :=
  mul_nonneg (mul_nonneg (hB.lam_nonneg x) (pow_nonneg (norm_nonneg _) _))
    (Real.rpow_nonneg (by linarith [hB.one_le_norm x]) _)

/-- Right of `1 + 2kW` the `k`-th tensor moment converges. -/
theorem summable_twistMomentTerm (hB : IsAbelianBase N lam ev) {z b : ι → ℂ} (χ : ι → C) {W : ℝ}
    (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) (k : ℕ) {σ : ℝ} (hσ : 1 + 2 * k * W < σ) :
    Summable (twistMomentTerm N lam ev z b χ k σ) := by
  set B := ∑ i, ‖b i‖
  have hs := (hB.summable_lam (σ - 2 * k * W) (by linarith)).mul_left (B ^ (2 * k))
  refine Summable.of_nonneg_of_le (twistMomentTerm_nonneg hB z b χ k σ) (fun x => ?_) hs
  have hN1 := hB.one_le_norm x
  have hN0 : 0 < N x := by linarith
  have hpow : ‖twistTrace N ev z b χ x‖ ^ (2 * k) ≤ B ^ (2 * k) * N x ^ (2 * k * W) := by
    calc ‖twistTrace N ev z b χ x‖ ^ (2 * k) ≤ (B * N x ^ W) ^ (2 * k) :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_twistTrace_le hB χ hW x) _
      _ = B ^ (2 * k) * N x ^ (2 * k * W) := by
          rw [mul_pow, ← Real.rpow_natCast (N x ^ W), ← Real.rpow_mul hN0.le]
          push_cast; ring_nf
  calc twistMomentTerm N lam ev z b χ k σ x
      = lam x * ‖twistTrace N ev z b χ x‖ ^ (2 * k) * N x ^ (-σ) := rfl
    _ ≤ lam x * (B ^ (2 * k) * N x ^ (2 * k * W)) * N x ^ (-σ) := by
        gcongr
        exact hB.lam_nonneg x
    _ = B ^ (2 * k) * (lam x * N x ^ (-(σ - 2 * k * W))) := by
        rw [show -(σ - 2 * k * W) = 2 * k * W + -σ by ring, Real.rpow_add hN0]
        ring

/-! ### Expansion over tuples of modes and characters -/

section Expansion

/-- The character of a tuple: `Π_j χ_{a_j}`. -/
def tupleChar (χ : ι → C) {k : ℕ} (a : Fin k → ι) : C := ∏ j, χ (a j)

/-- The character `χ_a χ_{a'}⁻¹` of a pair of tuples. -/
def pairChar (χ : ι → C) {k : ℕ} (a a' : Fin k → ι) : C := tupleChar χ a * (tupleChar χ a')⁻¹

omit [Fintype ι] in
theorem ev_prod_succ (hB : IsAbelianBase N lam ev) {m : ℕ} (f : Fin (m + 1) → C) (x : P) :
    ev (∏ j, f j) x = ∏ j, ev (f j) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ, hB.ev_mul, ih (fun j => f j.succ)]
    exact (Fin.prod_univ_succ (fun j => ev (f j) x)).symm

theorem ofReal_cpow_sum {r : ℝ} (hr : 0 < r) {k : ℕ} (w : Fin k → ℂ) :
    (r : ℂ) ^ (∑ j, w j) = ∏ j, (r : ℂ) ^ w j := by
  have h0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [Complex.cpow_def_of_ne_zero h0, Finset.mul_sum, Complex.exp_sum]

theorem conj_ofReal_cpow {r : ℝ} (hr : 0 < r) (w : ℂ) : conj ((r : ℂ) ^ w) = (r : ℂ) ^ conj w := by
  have h0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero h0, Complex.cpow_def_of_ne_zero h0, ← Complex.exp_conj, map_mul,
    ← Complex.ofReal_log hr.le, Complex.conj_ofReal]

/-- `t(x)^{m+1} = Σ_a (Π b_{a_j}) χ_a(x) N(x)^{Σ z_{a_j}}`. -/
theorem twistTrace_pow (hB : IsAbelianBase N lam ev) (z b : ι → ℂ) (χ : ι → C) {m : ℕ} (x : P) :
    twistTrace N ev z b χ x ^ (m + 1) = ∑ a : Fin (m + 1) → ι,
      tupleWeight b a * ev (tupleChar χ a) x * (N x : ℂ) ^ tupleMode z a := by
  have hN : 0 < N x := by linarith [hB.one_le_norm x]
  rw [twistTrace, ← Fin.prod_const, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, tupleWeight, tupleChar, tupleMode,
    ofReal_cpow_sum hN, ev_prod_succ hB]

/-- `|t(x)|^{2(m+1)} = Σ_{a,a'} B_{a,a'} (χ_a χ_{a'}⁻¹)(x) N(x)^{Z_{a,a'}}`. -/
theorem ofReal_norm_twistTrace_pow (hB : IsAbelianBase N lam ev) (z b : ι → ℂ) (χ : ι → C)
    {m : ℕ} (x : P) :
    ((‖twistTrace N ev z b χ x‖ ^ (2 * (m + 1)) : ℝ) : ℂ) =
      ∑ p : (Fin (m + 1) → ι) × (Fin (m + 1) → ι), pairWeight b p.1 p.2 *
        ev (pairChar χ p.1 p.2) x * (N x : ℂ) ^ pairMode z p.1 p.2 := by
  have hN : 0 < N x := by linarith [hB.one_le_norm x]
  have h0 : (N x : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : ((‖twistTrace N ev z b χ x‖ ^ 2 : ℝ) : ℂ) =
      twistTrace N ev z b χ x * conj (twistTrace N ev z b χ x) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [pow_mul, Complex.ofReal_pow, h2, mul_pow, ← map_pow, twistTrace_pow hB, map_sum,
    Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [map_mul, map_mul, conj_ofReal_cpow hN, hB.conj_ev, pairWeight, pairMode, pairChar, hB.ev_mul,
    Complex.cpow_add _ _ h0]
  ring

omit [Fintype ι] in
theorem summable_baseLSeries_term (hB : IsAbelianBase N lam ev) (ψ : C) {s : ℂ} (hs : 1 < s.re) :
    Summable fun x => (lam x : ℂ) * ev ψ x * (N x : ℂ) ^ (-s) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
    (hB.summable_lam s.re hs))
  have hN : 0 < N x := by linarith [hB.one_le_norm x]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hB.lam_nonneg x),
    Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re]
  calc lam x * ‖ev ψ x‖ * N x ^ (-s.re) ≤ lam x * 1 * N x ^ (-s.re) := by
        gcongr
        · exact hB.lam_nonneg x
        · exact hB.norm_ev_le ψ x
    _ = lam x * N x ^ (-s.re) := by ring

/-- **Coinvariants.** Right of the edge the tensor moment is `Σ_{a,a'} B_{a,a'} F_{χ_a χ_{a'}⁻¹}(σ − Z)`. -/
theorem ofReal_tsum_twistMomentTerm_eq_sum (hB : IsAbelianBase N lam ev) {z b : ι → ℂ}
    (χ : ι → C) {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) {m : ℕ} {σ : ℝ}
    (hσ : 1 + 2 * ((m + 1 : ℕ) : ℝ) * W < σ) :
    ((∑' x, twistMomentTerm N lam ev z b χ (m + 1) σ x : ℝ) : ℂ) =
      ∑ p : (Fin (m + 1) → ι) × (Fin (m + 1) → ι), pairWeight b p.1 p.2 *
        baseLSeries N lam ev (pairChar χ p.1 p.2) (σ - pairMode z p.1 p.2) := by
  have hsum : ∀ p : (Fin (m + 1) → ι) × (Fin (m + 1) → ι), Summable fun x =>
      pairWeight b p.1 p.2 * ((lam x : ℂ) * ev (pairChar χ p.1 p.2) x *
        (N x : ℂ) ^ (-((σ : ℂ) - pairMode z p.1 p.2))) := by
    intro p
    by_cases h : pairWeight b p.1 p.2 = 0
    · simp [h]
    · refine (summable_baseLSeries_term hB _ ?_).mul_left _
      rw [Complex.sub_re, Complex.ofReal_re]
      linarith [re_pairMode_le hW h]
  rw [Complex.ofReal_tsum]
  simp_rw [baseLSeries, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun p _ => hsum p]
  refine tsum_congr fun x => ?_
  have hN : 0 < N x := by linarith [hB.one_le_norm x]
  have h0 : (N x : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [twistMomentTerm, Complex.ofReal_mul, Complex.ofReal_mul, ofReal_norm_twistTrace_pow hB,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.ofReal_cpow hN.le, Complex.ofReal_neg,
    show -((σ : ℂ) - pairMode z p.1 p.2) = pairMode z p.1 p.2 + -(σ : ℂ) by ring,
    Complex.cpow_add _ _ h0]
  ring

end Expansion

/-! ### The edge -/

section Edge

/-- A function equal on `Re s > 1` to `G(s) + c/(s − 1)` with `G` continuous on `Re s ≥ 1`,
shifted by `Z` with `Re Z ≤ e − 1` and multiplied by `x − e`, tends to `c` if `Z = e − 1` and to
`0` otherwise as `x ↓ e`. -/
theorem tendsto_sub_mul_of_pole {F G : ℂ → ℂ} {c : ℂ} (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hF : ∀ s : ℂ, 1 < s.re → F s = G s + c / (s - 1)) {e : ℝ} {Z : ℂ} (hZ : Z.re ≤ e - 1) :
    Tendsto (fun x : ℝ => ((x - e : ℝ) : ℂ) * F (x - Z)) (𝓝[>] e)
      (𝓝 (if Z = ((e - 1 : ℝ) : ℂ) then c else 0)) := by
  have hev : ∀ᶠ x : ℝ in 𝓝[>] e, ((x - e : ℝ) : ℂ) * F (x - Z) =
      ((x - e : ℝ) : ℂ) * G (x - Z) +
        c * (((x - e : ℝ) : ℂ) / (((x - e : ℝ) : ℂ) + (((e - 1 : ℝ) : ℂ) - Z))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : 1 < ((x : ℂ) - Z).re := by
      rw [Complex.sub_re, Complex.ofReal_re]; linarith [Set.mem_Ioi.mp hx]
    rw [hF _ hx', mul_add]
    congr 1
    push_cast; ring
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have h0 : Tendsto (fun x : ℝ => ((x - e : ℝ) : ℂ)) (𝓝[>] e) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_sub_nhdsGT e)
    rw [Complex.ofReal_zero] at h
    exact h
  have hreg : Tendsto (fun x : ℝ => G (x - Z)) (𝓝[>] e) (𝓝 (G ((e : ℂ) - Z))) := by
    have hmem : ((e : ℂ) - Z) ∈ {s : ℂ | 1 ≤ s.re} := by
      simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.ofReal_re]; linarith
    refine (hG _ hmem).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
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
    have h3 := h1.add ((tendsto_const_nhds (x := (1 : ℂ))).congr' (EventuallyEq.symm h2) |>.const_mul c)
    simpa using h3
  · rw [if_neg hZe]
    have hd : ((e - 1 : ℝ) : ℂ) - Z ≠ 0 := sub_ne_zero.mpr (Ne.symm hZe)
    have h2 : Tendsto (fun x : ℝ => ((x - e : ℝ) : ℂ) / (((x - e : ℝ) : ℂ) +
        (((e - 1 : ℝ) : ℂ) - Z))) (𝓝[>] e) (𝓝 0) := by
      have := h0.div (h0.add_const (((e - 1 : ℝ) : ℂ) - Z)) (by rwa [zero_add])
      rw [zero_add, zero_div] at this
      exact this
    have h3 := h1.add (h2.const_mul c)
    simpa using h3

variable [DecidableEq C] {z b : ι → ℂ} {χ : ι → C} {k : ℕ}

/-- The **edge residue**: the weight of the pairs of tuples of mode `2kW` and trivial character. -/
def twistEdgeResidue (z b : ι → ℂ) (χ : ι → C) (k : ℕ) (W : ℝ) : ℂ :=
  ∑ p : (Fin k → ι) × (Fin k → ι),
    if pairMode z p.1 p.2 = ((2 * k * W : ℝ) : ℂ) ∧ pairChar χ p.1 p.2 = 1 then
      pairWeight b p.1 p.2 else 0

/-- `(σ − 1 − 2kW) D_k(σ)` tends to the edge residue as `σ ↓ 1 + 2kW`. -/
theorem tendsto_sub_mul_twistMoment (hB : IsAbelianBase N lam ev) {W : ℝ}
    (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) (hk : 1 ≤ k) :
    Tendsto (fun x : ℝ =>
        (((x - (1 + 2 * k * W)) * ∑' y, twistMomentTerm N lam ev z b χ k x y : ℝ) : ℂ))
      (𝓝[>] (1 + 2 * k * W)) (𝓝 (twistEdgeResidue z b χ k W)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (1 + 2 * ((m + 1 : ℕ) : ℝ) * W),
      ∑ p : (Fin (m + 1) → ι) × (Fin (m + 1) → ι), pairWeight b p.1 p.2 *
        (((x - (1 + 2 * ((m + 1 : ℕ) : ℝ) * W) : ℝ) : ℂ) *
          baseLSeries N lam ev (pairChar χ p.1 p.2) (x - pairMode z p.1 p.2)) =
      (((x - (1 + 2 * ((m + 1 : ℕ) : ℝ) * W)) *
        ∑' y, twistMomentTerm N lam ev z b χ (m + 1) x y : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Complex.ofReal_mul, ofReal_tsum_twistMomentTerm_eq_sum hB χ hW (Set.mem_Ioi.mp hx),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  refine Tendsto.congr' hev (tendsto_finsetSum _ fun p _ => ?_)
  by_cases hp : pairWeight b p.1 p.2 = 0
  · simp only [hp, zero_mul, ite_self]
    exact tendsto_const_nhds
  · have hZ : (pairMode z p.1 p.2).re ≤ (1 + 2 * ((m + 1 : ℕ) : ℝ) * W) - 1 := by
      linarith [re_pairMode_le hW hp]
    have he : (1 + 2 * ((m + 1 : ℕ) : ℝ) * W) - 1 = 2 * ((m + 1 : ℕ) : ℝ) * W := by ring
    by_cases hψ : pairChar χ p.1 p.2 = 1
    · obtain ⟨G, hGc, hGF⟩ := hB.pnt_one
      have hGF' : ∀ s : ℂ, 1 < s.re →
          baseLSeries N lam ev (pairChar χ p.1 p.2) s = G s + 1 / (s - 1) := by
        rw [hψ]; exact hGF
      have h := (tendsto_sub_mul_of_pole hGc hGF' hZ).const_mul (pairWeight b p.1 p.2)
      rw [he] at h
      convert h using 2
      split_ifs <;> simp_all
    · obtain ⟨G, hGc, hGF⟩ := hB.pnt_ne _ hψ
      have hGF' : ∀ s : ℂ, 1 < s.re →
          baseLSeries N lam ev (pairChar χ p.1 p.2) s = G s + 0 / (s - 1) := fun s hs => by
        rw [zero_div, add_zero]; exact hGF s hs
      have h := (tendsto_sub_mul_of_pole hGc hGF' hZ).const_mul (pairWeight b p.1 p.2)
      rw [he] at h
      convert h using 2
      split_ifs <;> simp_all

/-! ### The edge residue is a sum of squares -/

/-- The weight of all tuples of mode `κ.1` and character `κ.2`. -/
def twistModeWeight (z b : ι → ℂ) (χ : ι → C) (k : ℕ) (κ : ℂ × C) : ℂ :=
  ∑ a : Fin k → ι, if (tupleMode z a, tupleChar χ a) = κ then tupleWeight b a else 0

omit [Fintype ι] [DecidableEq C] in
theorem pairMode_pairChar_iff {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) {a a' : Fin k → ι}
    (h : pairWeight b a a' ≠ 0) :
    (pairMode z a a' = ((2 * k * W : ℝ) : ℂ) ∧ pairChar χ a a' = 1) ↔
      ((tupleMode z a, tupleChar χ a) = (tupleMode z a', tupleChar χ a') ∧
        (tupleMode z a).re = k * W) := by
  rw [pairMode_eq_iff hW h, pairChar, mul_inv_eq_one, Prod.mk.injEq]
  tauto

/-- **The edge residue is a sum of squares** over the modes and characters of top tuples. -/
theorem twistEdgeResidue_eq_sum_normSq {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) :
    twistEdgeResidue z b χ k W = ∑ κ ∈ (Finset.univ.filter fun a : Fin k → ι =>
        (tupleMode z a).re = k * W).image (fun a => (tupleMode z a, tupleChar χ a)),
      ((‖twistModeWeight z b χ k κ‖ ^ 2 : ℝ) : ℂ) := by
  classical
  set T := Finset.univ.filter fun a : Fin k → ι => (tupleMode z a).re = k * W
  set key : (Fin k → ι) → ℂ × C := fun a => (tupleMode z a, tupleChar χ a)
  have hterm : ∀ p : (Fin k → ι) × (Fin k → ι),
      (if pairMode z p.1 p.2 = ((2 * k * W : ℝ) : ℂ) ∧ pairChar χ p.1 p.2 = 1 then
        pairWeight b p.1 p.2 else 0) =
        if p.1 ∈ T ∧ key p.2 = key p.1 then pairWeight b p.1 p.2 else 0 := by
    intro p
    by_cases hp : pairWeight b p.1 p.2 = 0
    · simp [hp]
    · have := pairMode_pairChar_iff (χ := χ) hW hp
      simp only [T, key, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h1 : pairMode z p.1 p.2 = ((2 * k * W : ℝ) : ℂ) ∧ pairChar χ p.1 p.2 = 1
      · rw [if_pos h1, if_pos ⟨(this.mp h1).2, (this.mp h1).1.symm⟩]
      · rw [if_neg h1, if_neg fun h2 => h1 (this.mpr ⟨h2.2.symm, h2.1⟩)]
  rw [twistEdgeResidue, Finset.sum_congr rfl fun p _ => hterm p, ← Finset.univ_product_univ,
    Finset.sum_product]
  have hinner : ∀ a : Fin k → ι, (∑ a' : Fin k → ι,
      if a ∈ T ∧ key a' = key a then pairWeight b a a' else 0) =
      if a ∈ T then tupleWeight b a * conj (twistModeWeight z b χ k (key a)) else 0 := by
    intro a
    by_cases ha : a ∈ T
    · simp only [ha, true_and, if_true, twistModeWeight, map_sum, Finset.mul_sum, pairWeight]
      refine Finset.sum_congr rfl fun a' _ => ?_
      split_ifs <;> simp_all [key]
    · simp [ha]
  rw [Finset.sum_congr rfl fun a _ => hinner a, ← Finset.sum_filter,
    show (Finset.univ.filter fun a : Fin k → ι => a ∈ T) = T by ext a; simp]
  rw [← Finset.sum_fiberwise_of_maps_to (g := key) (t := T.image key)
    (fun a ha => Finset.mem_image_of_mem _ ha)]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp hκ
  have hfil : (T.filter fun a => key a = key a₀) = Finset.univ.filter fun a => key a = key a₀ := by
    ext a
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have h1 : tupleMode z a = tupleMode z a₀ := congrArg Prod.fst h
      rw [h1]
      exact (Finset.mem_filter.mp ha₀).2
  rw [Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.mp ha).2], ← Finset.sum_mul, hfil,
    Finset.sum_filter]
  rw [show (∑ a : Fin k → ι, if key a = key a₀ then tupleWeight b a else 0) =
      twistModeWeight z b χ k (key a₀) by simp only [twistModeWeight, key]]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

/-- **Nothing cancels at the edge.** For distinct pairs `(z_i, χ_i)` the edge residue is a positive
real number: the top tuples of largest imaginary mode carry a nonzero weight in some character,
because distinct characters are linearly independent. -/
theorem twistEdgeResidue_pos (hB : IsAbelianBase N lam ev) {W : ℝ}
    (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) (hWa : ∃ i, b i ≠ 0 ∧ (z i).re = W)
    (hinj : ∀ i j, b i ≠ 0 → b j ≠ 0 → z i = z j → χ i = χ j → i = j) (hk : 1 ≤ k) :
    ∃ r : ℝ, 0 < r ∧ twistEdgeResidue z b χ k W = r := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set Top := Finset.univ.filter fun i => b i ≠ 0 ∧ (z i).re = W
  obtain ⟨i₀, hi₀⟩ := hWa
  have hTop : Top.Nonempty := ⟨i₀, by simp [Top, hi₀.1, hi₀.2]⟩
  obtain ⟨is, his, hmax⟩ := Finset.exists_max_image Top (fun i => (z i).im) hTop
  have his' : b is ≠ 0 ∧ (z is).re = W := by simpa [Top] using his
  set c : Fin (m + 1) → ι := fun _ => is
  set Is := Finset.univ.filter fun i => b i ≠ 0 ∧ z i = z is
  -- a tuple of nonzero weight with the mode of the constant tuple runs in Is
  have hmem : ∀ a : Fin (m + 1) → ι, tupleMode z a = tupleMode z c → tupleWeight b a ≠ 0 →
      ∀ j, a j ∈ Is := by
    intro a hv hw
    have hb : ∀ j, b (a j) ≠ 0 := fun j => (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
    have hre : ∀ j, (z (a j)).re = W := by
      have h1 : ∑ j, (z (a j)).re = ∑ _j : Fin (m + 1), W := by
        have := congrArg Complex.re hv
        simp only [tupleMode, Complex.re_sum, c, his'.2] at this
        simpa using this
      exact fun j => (Finset.sum_eq_sum_iff_of_le fun j _ => hW _ (hb j)).mp h1 j
        (Finset.mem_univ j)
    have him : ∀ j, (z (a j)).im = (z is).im := by
      have hle : ∀ j ∈ Finset.univ, (z (a j)).im ≤ (z is).im := fun j _ =>
        hmax _ (by simp [Top, hb j, hre j])
      have h1 : ∑ j, (z (a j)).im = ∑ _j : Fin (m + 1), (z is).im := by
        have := congrArg Complex.im hv
        simpa [tupleMode, Complex.im_sum, c] using this
      exact fun j => (Finset.sum_eq_sum_iff_of_le hle).mp h1 j (Finset.mem_univ j)
    intro j
    simp only [Is, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hb j, Complex.ext (by rw [hre j, his'.2]) (him j)⟩
  -- some character carries a nonzero weight at the mode of the constant tuple
  have hex : ∃ g : C, twistModeWeight z b χ (m + 1) (tupleMode z c, g) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hpt : ∀ x, ∑ i ∈ Is, b i * ev (χ i) x = 0 := by
      intro x
      refine pow_eq_zero_iff (n := m + 1) (by omega) |>.mp ?_
      rw [← Fin.prod_const, Finset.prod_univ_sum]
      have hset : Fintype.piFinset (fun _ : Fin (m + 1) => Is) =
          Finset.univ.filter fun a => tupleMode z a = tupleMode z c ∧ tupleWeight b a ≠ 0 := by
        ext a
        simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ha
          have hz : ∀ j, z (a j) = z is := fun j => (Finset.mem_filter.mp (ha j)).2.2
          refine ⟨by simp [tupleMode, c, hz], ?_⟩
          exact Finset.prod_ne_zero_iff.mpr fun j _ => (Finset.mem_filter.mp (ha j)).2.1
        · exact fun h => hmem a h.1 h.2
      rw [hset, Finset.sum_filter]
      have hterm : ∀ a : Fin (m + 1) → ι, (if tupleMode z a = tupleMode z c ∧ tupleWeight b a ≠ 0
          then ∏ j, b (a j) * ev (χ (a j)) x else 0) =
          if tupleMode z a = tupleMode z c then tupleWeight b a * ev (tupleChar χ a) x else 0 := by
        intro a
        by_cases h1 : tupleMode z a = tupleMode z c
        · by_cases h2 : tupleWeight b a = 0
          · simp [h1, h2]
          · rw [if_pos ⟨h1, h2⟩, if_pos h1, Finset.prod_mul_distrib, tupleWeight, tupleChar,
              ev_prod_succ hB]
        · simp [h1]
      rw [Finset.sum_congr rfl fun a _ => hterm a]
      rw [← Finset.sum_fiberwise_of_maps_to (g := tupleChar χ) (t := Finset.univ.image (tupleChar χ))
        (fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a))]
      refine Finset.sum_eq_zero fun g _ => ?_
      have := hall g
      rw [twistModeWeight] at this
      calc ∑ a ∈ Finset.univ.filter (fun a => tupleChar χ a = g),
            (if tupleMode z a = tupleMode z c then tupleWeight b a * ev (tupleChar χ a) x else 0)
          = (∑ a, if (tupleMode z a, tupleChar χ a) = (tupleMode z c, g) then tupleWeight b a
              else 0) * ev g x := by
            rw [Finset.sum_filter, Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ => ?_
            by_cases h1 : tupleChar χ a = g
            · by_cases h2 : tupleMode z a = tupleMode z c <;> simp [h1, h2]
            · simp [h1]
        _ = 0 := by rw [this, zero_mul]
    -- linear independence of the characters
    have hcomb : ∑ g ∈ Is.image χ, (∑ i ∈ Is.filter (fun i => χ i = g), b i) • ev g = 0 := by
      funext x
      have h := hpt x
      rw [← Finset.sum_fiberwise_of_maps_to (g := χ) (t := Is.image χ)
        (fun i hi => Finset.mem_image_of_mem _ hi)] at h
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    have hzero := linearIndependent_iff'.mp hB.indep (Is.image χ) _ hcomb (χ is)
      (Finset.mem_image_of_mem _ (by simp [Is, his'.1]))
    have hsingle : Is.filter (fun i => χ i = χ is) = {is} := by
      ext i
      simp only [Is, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hb, hz⟩, hχ⟩
        exact hinj _ _ hb his'.1 hz hχ
      · rintro rfl
        exact ⟨⟨his'.1, rfl⟩, rfl⟩
    rw [hsingle, Finset.sum_singleton] at hzero
    exact his'.1 hzero
  obtain ⟨g, hg⟩ := hex
  -- the key of the constant tuple with character g is the key of a top tuple
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
  have hka : (tupleMode z a, tupleChar χ a) = (tupleMode z c, g) := by
    by_contra h
    exact ha (if_neg h)
  have haT : a ∈ Finset.univ.filter fun a : Fin (m + 1) → ι =>
      (tupleMode z a).re = ((m + 1 : ℕ) : ℝ) * W := by
    have h1 : tupleMode z a = tupleMode z c := congrArg Prod.fst hka
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [h1]
    simp [c, tupleMode, his'.2]
  refine ⟨∑ κ ∈ (Finset.univ.filter fun a : Fin (m + 1) → ι =>
      (tupleMode z a).re = ((m + 1 : ℕ) : ℝ) * W).image (fun a => (tupleMode z a, tupleChar χ a)),
      ‖twistModeWeight z b χ (m + 1) κ‖ ^ 2, ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (fun κ _ => sq_nonneg ‖twistModeWeight z b χ (m + 1) κ‖) (Finset.mem_image_of_mem _ haT))
    rw [hka]
    exact pow_pos (norm_pos_iff.mpr hg) 2
  · rw [twistEdgeResidue_eq_sum_normSq hW, Complex.ofReal_sum]

/-! ### Base loss exactly one -/

omit [DecidableEq C] in
/-- **Base loss exactly one.** On an abelian base, a twisted flow datum with distinct pairs
`(z_i, χ_i)` and width `W` has `k`-th tensor moment converging exactly right of `1 + 2kW`. -/
theorem summable_twistMomentTerm_iff (hB : IsAbelianBase N lam ev) {W : ℝ}
    (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) (hWa : ∃ i, b i ≠ 0 ∧ (z i).re = W)
    (hinj : ∀ i j, b i ≠ 0 → b j ≠ 0 → z i = z j → χ i = χ j → i = j) (hk : 1 ≤ k) (σ : ℝ) :
    Summable (twistMomentTerm N lam ev z b χ k σ) ↔ 1 + 2 * k * W < σ := by
  classical
  refine ⟨fun hs => ?_, summable_twistMomentTerm hB χ hW k⟩
  by_contra hσ
  push Not at hσ
  set e := 1 + 2 * k * W
  obtain ⟨r, hr, hres⟩ := twistEdgeResidue_pos hB hW hWa hinj hk
  set M := ∑' y, twistMomentTerm N lam ev z b χ k σ y
  have hbound : ∀ x : ℝ, e < x → ∑' y, twistMomentTerm N lam ev z b χ k x y ≤ M := by
    intro x hx
    have hle : ∀ y, twistMomentTerm N lam ev z b χ k x y ≤ twistMomentTerm N lam ev z b χ k σ y := by
      intro y
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hB.lam_nonneg y)
        (pow_nonneg (norm_nonneg _) _))
      exact Real.rpow_le_rpow_of_exponent_le (hB.one_le_norm y) (by linarith)
    exact Summable.tsum_le_tsum hle (summable_twistMomentTerm hB χ hW k hx) hs
  have hlim := tendsto_sub_mul_twistMoment (χ := χ) hB hW hk
  rw [hres] at hlim
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  have hup : Tendsto (fun x : ℝ => (x - e) * M) (𝓝[>] e) (𝓝 0) := by
    have h := (tendsto_sub_nhdsGT e).mul_const M
    rwa [zero_mul] at h
  have hle : ∀ᶠ x : ℝ in 𝓝[>] e,
      (x - e) * ∑' y, twistMomentTerm N lam ev z b χ k x y ≤ (x - e) * M := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_le_mul_of_nonneg_left (hbound x hx) (sub_pos.mpr hx).le
  have := le_of_tendsto_of_tendsto hre hup hle
  linarith

omit [DecidableEq C] in
/-- **The pole law is the conclusion.** On an abelian base a bound `D_k(2kw₀ + A) < ∞` for every
`k ≥ 1`, with `A` independent of `k`, holds iff the width is at most `w₀`. -/
theorem exists_twistPoleLaw_iff (hB : IsAbelianBase N lam ev) {W : ℝ}
    (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W) (hWa : ∃ i, b i ≠ 0 ∧ (z i).re = W)
    (hinj : ∀ i j, b i ≠ 0 → b j ≠ 0 → z i = z j → χ i = χ j → i = j) (w₀ : ℝ) :
    (∃ A : ℝ, ∀ k : ℕ, 1 ≤ k → Summable (twistMomentTerm N lam ev z b χ k (2 * k * w₀ + A))) ↔
      W ≤ w₀ := by
  constructor
  · rintro ⟨A, hA⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((A - 1) / (2 * (W - w₀))))
    have hk1 : 1 ≤ k := by
      have : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
      exact_mod_cast this.le
    have h := (summable_twistMomentTerm_iff hB hW hWa hinj hk1 _).mp (hA k hk1)
    have hk2 : (A - 1) / (2 * (W - w₀)) < k := (le_max_right _ _).trans_lt hk
    rw [div_lt_iff₀ (by linarith)] at hk2
    nlinarith
  · intro hle
    refine ⟨2, fun k _ => summable_twistMomentTerm hB χ hW k ?_⟩
    have : (2 * k * W : ℝ) ≤ 2 * k * w₀ :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    linarith

end Edge

/-! ### Dirichlet twists over `Spec ℤ` -/

section Dirichlet

/-- The norm `max(n, 1)` of the point `n` (the point `0` has weight `Λ(0) = 0`). -/
def dirichletNorm (n : ℕ) : ℝ := max (n : ℝ) 1

/-- Dirichlet characters evaluated at the integers. -/
def dirichletEv (q : ℕ) (ψ : DirichletCharacter ℂ q) (n : ℕ) : ℂ := ψ n

theorem dirichlet_tsum_eq_LSeries {q : ℕ} (ψ : DirichletCharacter ℂ q) (s : ℂ) :
    ∑' n, ((Λ n : ℝ) : ℂ) * dirichletEv q ψ n * ((dirichletNorm n : ℝ) : ℂ) ^ (-s) =
      LSeries (↗ψ * ↗Λ) s := by
  rw [LSeries]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, dirichletNorm,
      max_eq_left (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn), Complex.ofReal_natCast,
      Complex.cpow_neg, Pi.mul_apply, div_eq_mul_inv, dirichletEv]
    ring

theorem dirichletEv_mul {q : ℕ} (ψ ψ' : DirichletCharacter ℂ q) (n : ℕ) :
    dirichletEv q (ψ * ψ') n = dirichletEv q ψ n * dirichletEv q ψ' n := by
  show (ψ * ψ') (n : ZMod q) = ψ n * ψ' n
  rw [MulChar.coeToFun_mul]
  rfl

theorem conj_dirichletEv {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (n : ℕ) :
    conj (dirichletEv q ψ n) = dirichletEv q ψ⁻¹ n := by
  rw [starRingEnd_apply]
  exact MulChar.star_apply' ψ (n : ZMod q)

theorem neg_div_eq_trivChar_aux {A A' s : ℂ} (hA : A ≠ 0) (hs : s - 1 ≠ 0) :
    -A' / A = -((s - 1) * A' + A) / ((s - 1) * A) + 1 / (s - 1) := by
  field_simp
  ring

/-- The prime number theorem of the trivial character: `L(Λ 1_q, s) = G(s) + 1/(s − 1)`. -/
theorem dirichlet_pnt_one (q : ℕ) [NeZero q] :
    ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      baseLSeries dirichletNorm (fun n => Λ n) (dirichletEv q) 1 s = G s + 1 / (s - 1) := by
  refine ⟨fun s => -deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
    DirichletCharacter.LFunctionTrivChar₁ q s, ?_, fun s hs => ?_⟩
  · refine (DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁ q).mono fun s hs => ?_
    simp only [Set.mem_setOf_eq] at hs ⊢
    rcases eq_or_ne s 1 with rfl | hs1
    · exact Or.inl rfl
    · exact Or.inr (DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (.inr hs1) hs)
  · have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
    have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (.inr hs1) hs.le
    rw [baseLSeries, dirichlet_tsum_eq_LSeries, DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hs,
      ← DirichletCharacter.LFunction_eq_LSeries _ hs,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hs]
    beta_reduce
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1,
      DirichletCharacter.LFunctionTrivChar]
    exact neg_div_eq_trivChar_aux hL (sub_ne_zero.mpr hs1)

/-- The prime number theorem of a nontrivial character: `L(Λ ψ, s)` is continuous on `Re s ≥ 1`. -/
theorem dirichlet_pnt_ne {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) :
    ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      baseLSeries dirichletNorm (fun n => Λ n) (dirichletEv q) ψ s = G s := by
  refine ⟨fun s => -deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s,
    ?_, fun s hs => ?_⟩
  · exact (DirichletCharacter.continuousOn_neg_logDeriv_LFunction_of_nontriv hψ).mono
      fun s hs => DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (.inl hψ) hs
  · rw [baseLSeries, dirichlet_tsum_eq_LSeries, DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hs,
      ← DirichletCharacter.LFunction_eq_LSeries _ hs,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hs]

/-- Distinct Dirichlet characters are linearly independent as functions on `ℕ`. -/
theorem linearIndependent_dirichletEv (q : ℕ) [NeZero q] :
    LinearIndependent ℂ (dirichletEv q) := by
  have h1 := linearIndependent_monoidHom (ZMod q) ℂ
  have h2 : LinearIndependent ℂ (fun ψ : DirichletCharacter ℂ q =>
      ((ψ.toMonoidHom : ZMod q →* ℂ) : ZMod q → ℂ)) :=
    h1.comp (fun ψ : DirichletCharacter ℂ q => ψ.toMonoidHom) fun ψ ψ' h =>
      MulChar.ext' fun a => DFunLike.congr_fun h a
  have hinj := LinearMap.funLeft_injective_of_surjective ℂ ℂ (fun n : ℕ => (n : ZMod q))
    ZMod.natCast_zmod_surjective
  have h3 := h2.map' (LinearMap.funLeft ℂ ℂ (fun n : ℕ => (n : ZMod q)))
    (LinearMap.ker_eq_bot.mpr hinj)
  have heq : (LinearMap.funLeft ℂ ℂ (fun n : ℕ => (n : ZMod q))) ∘
      (fun ψ : DirichletCharacter ℂ q => ((ψ.toMonoidHom : ZMod q →* ℂ) : ZMod q → ℂ)) =
      dirichletEv q := by
    funext ψ n
    rfl
  rwa [heq] at h3

theorem summable_dirichletLam {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => Λ n * dirichletNorm n ^ (-σ) := by
  refine (summable_vonMangoldt_rpow hσ).congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [dirichletNorm, max_eq_left (by exact_mod_cast hn)]

/-- **Dirichlet characters form an abelian base over `Spec ℤ`.** -/
theorem isAbelianBase_dirichlet (q : ℕ) [NeZero q] :
    IsAbelianBase dirichletNorm (fun n => Λ n) (dirichletEv q) where
  one_le_norm _ := le_max_right _ _
  lam_nonneg _ := vonMangoldt_nonneg
  summable_lam _ hσ := summable_dirichletLam hσ
  norm_ev_le ψ _ := DirichletCharacter.norm_le_one ψ _
  ev_mul := dirichletEv_mul
  conj_ev := conj_dirichletEv
  pnt_one := dirichlet_pnt_one q
  pnt_ne := dirichlet_pnt_ne
  indep := linearIndependent_dirichletEv q

/-- **Dirichlet twists are a ruler.** A flow datum over `Spec ℤ` twisted by Dirichlet characters,
with distinct pairs `(z_i, χ_i)` and width `W`, has `k`-th tensor moment
`Σ Λ(n) |Σ_i b_i χ_i(n) n^{z_i}|^{2k} n^{−σ}` converging exactly for `σ > 1 + 2kW`. -/
theorem summable_dirichletMomentTerm_iff {q : ℕ} [NeZero q] {z b : ι → ℂ}
    {χ : ι → DirichletCharacter ℂ q} {W : ℝ} (hW : ∀ i, b i ≠ 0 → (z i).re ≤ W)
    (hWa : ∃ i, b i ≠ 0 ∧ (z i).re = W)
    (hinj : ∀ i j, b i ≠ 0 → b j ≠ 0 → z i = z j → χ i = χ j → i = j) {k : ℕ} (hk : 1 ≤ k)
    (σ : ℝ) :
    Summable (twistMomentTerm dirichletNorm (fun n => Λ n) (dirichletEv q) z b χ k σ) ↔
      1 + 2 * k * W < σ :=
  summable_twistMomentTerm_iff (isAbelianBase_dirichlet q) hW hWa hinj hk σ

end Dirichlet

end GaloisForLFunctions.TensorPowerProgramme
