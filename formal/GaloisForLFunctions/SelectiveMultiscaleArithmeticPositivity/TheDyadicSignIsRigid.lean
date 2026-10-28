import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.OnNonnegativeTestsZetaIsTheWorstTwin
import GaloisForLFunctions.RHTower.XiMassShellPrimeMass
import GaloisForLFunctions.RHTower.ThetaPrimeScheduleSpectralObservation

/-!
# The dyadic sign of one generator is rigid

Weil's form on the dyadic tower `g, T_{log 2} g, T_{2 log 2} g, …` of one generator is a Toeplitz
form in the lag (`weilGram_tower_apply`): the entry of levels `i, j` is `W_λ(T_{(i−j) log 2} k)`,
`k = g ⋆ g̃`. Positivity of the single window `{0, d}` bounds the symmetrized lag correlation by the
diagonal (`norm_lagSym_le`): `‖W(T_{−D}k) + conj W(T_D k)‖ ≤ 2 Re W(k)`, `D = d log 2`.

Two weights share the archimedean and pole terms, so their lag correlations differ by the prime
pairing of the difference `u = λ' − λ` alone (`lagW_sub`). This gives:

* **Rigidity** (`primeMass_add_le_of_dyadicPositive`): if `λ` and `λ'` are both dyadic positive
  along `g`, the dyadic prime mass of `u` at every lag is at most `2 Re W_λ(k) + 2 Re W_{λ'}(k)`.
* For a nonnegative generator and a one-signed difference the prime mass is a sum of nonnegative
  terms, so unbounded mass along the lags excludes that both weights are dyadic positive
  (`not_dyadicPositive_and_of_unbounded`). The failing window is `{0, d}` at the first lag where
  the mass exceeds the two diagonals.
* **Brun–Titchmarsh and short-interval prime number theorems do not decide the sign**
  (`not_dyadicPositive_vonMangoldt_and_perturbed`): `Λ` and `Λ + ε n^{−η}`, `0 < η < 1/2`, are
  never both dyadic positive, although their partial sums on every interval `(a, b]` differ by at
  most `ε (b − a) a^{−η}` (`sum_perturbation_Ioc_le`). Any statement on primes in intervals that is
  stable under a relative error `o(1)` holds for both.
* **Selectivity** (`not_dyadicPositive_vonMangoldt_and_liouvilleTwin`): `Λ` and its Liouville twin
  are never both dyadic positive along a nonnegative generator; their difference `2 log p` on the
  primes has dyadic mass of order `2^{d/2}` by the prime number theorem.
-/

open Complex Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry RHTower

noncomputable section

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open ArithmeticCastelnuovoSeveri (weilGram cx)

local notation "Tr" => ArithmeticCastelnuovoSeveri.translate

/-! ### Dyadic towers and their lag correlations -/

/-- Dyadic positivity of a weight along a generator: every finite window of the `T_{log 2}`-tower
has a Weil Gram matrix without negative squares. -/
def DyadicPositive (lam : ℕ → ℝ) (g : ℝ → ℂ) : Prop :=
  ∀ K : Finset ℤ, hermNegIndex (weilGram lam fun k : K => Tr ((k : ℤ) * Real.log 2) g) = 0

/-- The lag correlation `W_λ(T_s k)`, `k = g ⋆ g̃`. -/
def lagW (lam : ℕ → ℝ) (g : ℝ → ℂ) (s : ℝ) : ℂ :=
  weilFullFunctional lam (Tr s (EF.weilTest g g))

/-- **Tower Grams are Toeplitz**: the entry of levels `i, j` is the lag correlation at
`(i − j) ℓ`. -/
theorem weilGram_tower_apply (lam : ℕ → ℝ) (g : ℝ → ℂ) (ℓ : ℝ) (K : Finset ℤ) (i j : K) :
    weilGram lam (fun k : K => Tr ((k : ℤ) * ℓ) g) i j =
      lagW lam g ((((i : ℤ) : ℝ) - ((j : ℤ) : ℝ)) * ℓ) := by
  unfold weilGram lagW
  congr 1
  funext u
  rw [ArithmeticCastelnuovoSeveri.weilTest_translate]
  simp only [ArithmeticCastelnuovoSeveri.translate]
  congr 1
  ring

/-! ### A `2 × 2` window bounds the lag correlation -/

theorem hermQuad_smul {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (x : ι → ℂ) :
    hermQuad H (c • x) = Complex.normSq c * hermQuad H x := by
  unfold hermQuad
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.re_ofReal_mul]

/-- Without negative squares the Hermitian quadratic form is nonnegative. -/
theorem hermQuad_nonneg_of_hermNegIndex_eq_zero {ι : Type*} [Fintype ι] {H : Matrix ι ι ℂ}
    (h : hermNegIndex H = 0) (x : ι → ℂ) : 0 ≤ hermQuad H x := by
  by_contra hneg
  push Not at hneg
  have hx : x ≠ 0 := by
    rintro rfl
    simp [hermQuad] at hneg
  have hpd : IsPosDefOn (-H) (Submodule.span ℂ {x}) := by
    intro y hy hy0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hc : c ≠ 0 := by
      rintro rfl
      exact hy0 (zero_smul ℂ x)
    rw [hermQuad_smul, hermQuad_neg]
    exact mul_pos (Complex.normSq_pos.mpr hc) (by linarith)
  have h1 := finrank_le_posIndex hpd
  rw [finrank_span_singleton hx] at h1
  unfold hermNegIndex at h
  omega

/-- The quadratic form at `e_i + z e_j`. -/
theorem dotProduct_single_add_single {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (i j : ι) (z : ℂ) :
    star (Pi.single i 1 + Pi.single j z) ⬝ᵥ H *ᵥ (Pi.single i 1 + Pi.single j z) =
      H i i + H i j * z + conj z * H j i + conj z * H j j * z := by
  have hcol : ∀ (k : ι) (w : ℂ), H *ᵥ Pi.single k w = fun a => H a k * w := fun k w => by
    funext a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [star_add, ← Pi.single_star, ← Pi.single_star, Matrix.mulVec_add, hcol, hcol, add_dotProduct,
    single_dotProduct, single_dotProduct]
  simp only [Pi.add_apply, star_one, one_mul, Complex.star_def]
  ring

/-- **The `2 × 2` window bound**: `‖H_{ij} + conj H_{ji}‖ ≤ Re H_{ii} + Re H_{jj}`. -/
theorem norm_add_conj_le_of_hermNegIndex_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (h : hermNegIndex H = 0) {i j : ι} (hij : i ≠ j) :
    ‖H i j + conj (H j i)‖ ≤ (H i i).re + (H j j).re := by
  set S := H i j + conj (H j i) with hS_def
  have hii : 0 ≤ (H i i).re := by
    have h0 := hermQuad_nonneg_of_hermNegIndex_eq_zero h (Pi.single i 1)
    simpa [hermQuad, Matrix.mulVec_single, Pi.star_single] using h0
  have hjj : 0 ≤ (H j j).re := by
    have h0 := hermQuad_nonneg_of_hermNegIndex_eq_zero h (Pi.single j 1)
    simpa [hermQuad, Matrix.mulVec_single, Pi.star_single] using h0
  rcases eq_or_ne S 0 with hS | hS
  · rw [hS, norm_zero]
    linarith
  have hSpos : 0 < ‖S‖ := norm_pos_iff.mpr hS
  set z : ℂ := -(conj S / (‖S‖ : ℂ)) with hz_def
  have hq := hermQuad_nonneg_of_hermNegIndex_eq_zero h (Pi.single i 1 + Pi.single j z)
  unfold hermQuad at hq
  rw [dotProduct_single_add_single H i j z] at hq
  have hzz : conj z * z = 1 := by
    rw [hz_def, map_neg, map_div₀, Complex.conj_conj, Complex.conj_ofReal, neg_mul_neg,
      div_mul_div_comm, mul_comm S, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have : (‖S‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hSpos.ne'
    field_simp
    push_cast
    ring
  have hzS : z * S = -((‖S‖ : ℝ) : ℂ) := by
    have hS0 : ((‖S‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hSpos.ne'
    rw [hz_def, neg_mul, div_mul_eq_mul_div, mul_comm (conj S), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    field_simp
    push_cast
    ring
  have hcross : (H i j * z + conj z * H j i).re = -‖S‖ := by
    have e : H i j * z + conj z * H j i = z * S + (conj z * H j i - z * conj (H j i)) := by
      rw [hS_def]; ring
    have him : (conj z * H j i - z * conj (H j i)).re = 0 := by
      have : z * conj (H j i) = conj (conj z * H j i) := by simp [map_mul, mul_comm]
      rw [this, Complex.sub_re, Complex.conj_re, sub_self]
    rw [e, Complex.add_re, him, add_zero, hzS, Complex.neg_re, Complex.ofReal_re]
  have hdiag : (conj z * H j j * z).re = (H j j).re := by
    have : conj z * H j j * z = (conj z * z) * H j j := by ring
    rw [this, hzz, one_mul]
  have hsplit : (H i i + H i j * z + conj z * H j i + conj z * H j j * z).re =
      (H i i).re + (H i j * z + conj z * H j i).re + (conj z * H j j * z).re := by
    simp only [Complex.add_re]; ring
  rw [hsplit, hcross, hdiag] at hq
  linarith

/-- **One window bounds the lag**: if `λ` is dyadic positive along `g`, then for every lag
`d ≠ 0`, `‖W(T_{−D}k) + conj W(T_D k)‖ ≤ 2 Re W(k)`, `D = d log 2`. -/
theorem norm_lagSym_le {lam : ℕ → ℝ} {g : ℝ → ℂ} (h : DyadicPositive lam g) {d : ℤ} (hd : d ≠ 0) :
    ‖lagW lam g (-((d : ℝ) * Real.log 2)) + conj (lagW lam g ((d : ℝ) * Real.log 2))‖ ≤
      2 * (lagW lam g 0).re := by
  classical
  set K : Finset ℤ := {0, d}
  have h0 : (0 : ℤ) ∈ K := by simp [K]
  have hd' : d ∈ K := by simp [K]
  have hij : (⟨0, h0⟩ : K) ≠ ⟨d, hd'⟩ := fun e => hd (congrArg Subtype.val e).symm
  have hb := norm_add_conj_le_of_hermNegIndex_eq_zero (h K) hij
  simp only [weilGram_tower_apply, Int.cast_zero, zero_sub, sub_zero, sub_self, zero_mul,
    neg_mul] at hb
  linarith

/-! ### Two weights differ only by their prime pairing -/

theorem hasCompactSupport_translate_weilTest {g : ℝ → ℂ} (hgc : HasCompactSupport g) (s : ℝ) :
    HasCompactSupport (Tr s (EF.weilTest g g)) :=
  ArithmeticCastelnuovoSeveri.translate_hasCompactSupport (EF.weilTest_hasCompactSupport hgc hgc) s

/-- The lag correlations of two weights differ by the prime pairing of their difference. -/
theorem lagW_sub (lam lam' : ℕ → ℝ) {g : ℝ → ℂ} (hgc : HasCompactSupport g) (s : ℝ) :
    lagW lam' g s - lagW lam g s =
      -∑' n : ℕ, ((if 2 ≤ n then (lam' n - lam n) / Real.sqrt n else 0 : ℝ) : ℂ) *
        (Tr s (EF.weilTest g g) (Real.log n) + Tr s (EF.weilTest g g) (-Real.log n)) := by
  have hk := hasCompactSupport_translate_weilTest hgc s
  unfold lagW
  rw [weilFullFunctional_eq_sub lam' hk, weilFullFunctional_eq_sub lam hk]
  have hsub := (summable_primeAtoms (fun n => if 2 ≤ n then
      (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) / Real.sqrt n else 0) hk).tsum_sub
    (summable_primeAtoms (fun n => if 2 ≤ n then
      (lam' n - (ArithmeticFunction.vonMangoldt n : ℝ)) / Real.sqrt n else 0) hk)
  rw [show ∀ L A B : ℂ, L - B - (L - A) = A - B from fun _ _ _ => by ring, ← hsub, ← tsum_neg]
  congr 1
  funext n
  by_cases hn : 2 ≤ n
  · simp only [if_pos hn]; push_cast; ring
  · simp only [if_neg hn]; push_cast; ring

/-- The **dyadic prime mass** of a weight difference `u` at lag `s`. -/
def primeMass (u : ℕ → ℝ) (g : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then u n / Real.sqrt n else 0) *
    ((Tr s (EF.weilTest g g) (Real.log n)).re + (Tr s (EF.weilTest g g) (-Real.log n)).re)

theorem re_lagW_sub (lam lam' : ℕ → ℝ) {g : ℝ → ℂ} (hgc : HasCompactSupport g) (s : ℝ) :
    (lagW lam' g s - lagW lam g s).re = -primeMass (fun n => lam' n - lam n) g s := by
  rw [lagW_sub lam lam' hgc s, Complex.neg_re,
    Complex.re_tsum (summable_primeAtoms _ (hasCompactSupport_translate_weilTest hgc s))]
  congr 1
  refine tsum_congr fun n => ?_
  rw [Complex.re_ofReal_mul, Complex.add_re]

/-- **Rigidity of the dyadic sign.** If two weights are dyadic positive along `g`, the dyadic prime
mass of their difference at every lag is bounded by the two diagonals. -/
theorem primeMass_add_le_of_dyadicPositive {lam lam' : ℕ → ℝ} {g : ℝ → ℂ}
    (hgc : HasCompactSupport g) (h : DyadicPositive lam g) (h' : DyadicPositive lam' g) {d : ℤ}
    (hd : d ≠ 0) :
    primeMass (fun n => lam' n - lam n) g (-((d : ℝ) * Real.log 2)) +
        primeMass (fun n => lam' n - lam n) g ((d : ℝ) * Real.log 2) ≤
      2 * ((lagW lam g 0).re + (lagW lam' g 0).re) := by
  set D : ℝ := (d : ℝ) * Real.log 2
  set S := lagW lam g (-D) + conj (lagW lam g D)
  set S' := lagW lam' g (-D) + conj (lagW lam' g D)
  have hre : (S' - S).re = -(primeMass (fun n => lam' n - lam n) g (-D) +
      primeMass (fun n => lam' n - lam n) g D) := by
    have e : S' - S = (lagW lam' g (-D) - lagW lam g (-D)) +
        conj (lagW lam' g D - lagW lam g D) := by
      simp only [S, S', map_sub]; ring
    rw [e, Complex.add_re, Complex.conj_re, re_lagW_sub lam lam' hgc, re_lagW_sub lam lam' hgc]
    ring
  have hle : -(S' - S).re ≤ ‖S'‖ + ‖S‖ :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (norm_sub_le _ _))
  have h1 := norm_lagSym_le h hd
  have h2 := norm_lagSym_le h' hd
  rw [hre, neg_neg] at hle
  linarith

/-! ### Nonnegative generators -/

theorem primeMass_nonneg {u : ℕ → ℝ} (hu : ∀ n, 2 ≤ n → 0 ≤ u n) {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (s : ℝ) : 0 ≤ primeMass u (cx f) s := by
  refine tsum_nonneg fun n => mul_nonneg ?_ (add_nonneg ?_ ?_)
  · split_ifs with hn
    · exact div_nonneg (hu n hn) (Real.sqrt_nonneg _)
    · exact le_rfl
  · exact ArithmeticCorrespondencePositivity.re_weilTest_nonneg hf _
  · exact ArithmeticCorrespondencePositivity.re_weilTest_nonneg hf _

/-- **Unbounded mass excludes a pair.** For a nonnegative generator and weights `λ ≤ λ'`, if the
dyadic prime mass of `λ' − λ` is unbounded along the lags, `λ` and `λ'` are not both dyadic
positive. -/
theorem not_dyadicPositive_and_of_unbounded {lam lam' : ℕ → ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfc : HasCompactSupport (cx f)) (hu : ∀ n, 2 ≤ n → lam n ≤ lam' n)
    (hunb : ∀ M : ℝ, ∃ d : ℕ, 1 ≤ d ∧
      M < primeMass (fun n => lam' n - lam n) (cx f) ((d : ℝ) * Real.log 2)) :
    ¬ (DyadicPositive lam (cx f) ∧ DyadicPositive lam' (cx f)) := by
  rintro ⟨h, h'⟩
  obtain ⟨d, hd1, hM⟩ := hunb (2 * ((lagW lam (cx f) 0).re + (lagW lam' (cx f) 0).re))
  have hd : ((d : ℤ)) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hb := primeMass_add_le_of_dyadicPositive hfc h h' hd
  have hn := primeMass_nonneg (u := fun n => lam' n - lam n)
    (fun n hn => sub_nonneg.mpr (hu n hn)) hf (-(((d : ℤ) : ℝ) * Real.log 2))
  push_cast at hb hn
  linarith

/-- A nonnegative nonzero `C²` generator has autocorrelation bounded below near the origin. -/
theorem exists_re_weilTest_ge {f : ℝ → ℝ} (hf : ContDiff ℝ 2 (cx f))
    (hfc : HasCompactSupport (cx f)) (hne : ∃ x, f x ≠ 0) :
    ∃ r > 0, ∃ c > 0, ∀ x : ℝ, |x| ≤ r → c ≤ (EF.weilTest (cx f) (cx f) x).re := by
  have hcont : Continuous fun x => (EF.weilTest (cx f) (cx f) x).re :=
    Complex.continuous_re.comp (EF.weilTest_contDiff hf hf.continuous hfc).continuous
  have hfcont : Continuous f := by
    have : f = fun x => (cx f x).re := by funext x; simp [cx]
    rw [this]; exact Complex.continuous_re.comp hf.continuous
  have h0 : 0 < (EF.weilTest (cx f) (cx f) 0).re := by
    rw [WeilSpectral.weilTest_apply]
    have e : (fun u => cx f u * conj (cx f (u - 0))) = fun u => ((f u * f u : ℝ) : ℂ) := by
      funext u; simp [cx]
    rw [e, integral_complex_ofReal, Complex.ofReal_re]
    obtain ⟨x0, hx0⟩ := hne
    have hfc' : HasCompactSupport f := by
      have : f = fun x => (cx f x).re := by funext x; simp [cx]
      rw [this]; exact hfc.comp_left Complex.zero_re
    refine (hfcont.mul hfcont).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hfc'.mul_left) (fun u => mul_self_nonneg _) (x := x0) (mul_self_ne_zero.mpr hx0)
  set c := (EF.weilTest (cx f) (cx f) 0).re / 2
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), c < (EF.weilTest (cx f) (cx f) x).re :=
    hcont.continuousAt.eventually (lt_mem_nhds (by simp only [c]; linarith))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r / 2, half_pos hr, c, by simp only [c]; linarith, fun x hx => (hball ?_).le⟩
  rw [Real.dist_eq, sub_zero]
  linarith

/-- Lower bound of the dyadic prime mass by the weights on one window `|log n − D| ≤ r`. -/
theorem primeMass_ge_window {u : ℕ → ℝ} (hu : ∀ n, 2 ≤ n → 0 ≤ u n) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfc : HasCompactSupport (cx f)) {r c : ℝ}
    (hc : ∀ x : ℝ, |x| ≤ r → c ≤ (EF.weilTest (cx f) (cx f) x).re) (D : ℝ) (W : Finset ℕ)
    (hW : ∀ n ∈ W, 2 ≤ n ∧ |Real.log n - D| ≤ r) :
    c * ∑ n ∈ W, u n / Real.sqrt n ≤ primeMass u (cx f) D := by
  have hterm : ∀ n : ℕ, 0 ≤ (if 2 ≤ n then u n / Real.sqrt n else 0) *
      ((Tr D (EF.weilTest (cx f) (cx f)) (Real.log n)).re +
        (Tr D (EF.weilTest (cx f) (cx f)) (-Real.log n)).re) := fun n =>
    mul_nonneg (by split_ifs with hn; exacts [div_nonneg (hu n hn) (Real.sqrt_nonneg _), le_rfl])
      (add_nonneg (ArithmeticCorrespondencePositivity.re_weilTest_nonneg hf0 _)
        (ArithmeticCorrespondencePositivity.re_weilTest_nonneg hf0 _))
  have hsum : Summable fun n : ℕ => (if 2 ≤ n then u n / Real.sqrt n else 0) *
      ((Tr D (EF.weilTest (cx f) (cx f)) (Real.log n)).re +
        (Tr D (EF.weilTest (cx f) (cx f)) (-Real.log n)).re) := by
    have hs := summable_primeAtoms (fun n => if 2 ≤ n then u n / Real.sqrt n else 0)
      (hasCompactSupport_translate_weilTest hfc D)
    refine (Complex.reCLM.summable hs).congr fun n => ?_
    simp only [Complex.reCLM_apply, Complex.re_ofReal_mul, Complex.add_re]
  rw [Finset.mul_sum]
  refine le_trans ?_ (hsum.sum_le_tsum W fun n _ => hterm n)
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨h2, hlog⟩ := hW n hn
  rw [if_pos h2]
  have hwn : 0 ≤ u n / Real.sqrt n := div_nonneg (hu n h2) (Real.sqrt_nonneg _)
  have hk1 : c ≤ (Tr D (EF.weilTest (cx f) (cx f)) (Real.log n)).re := hc _ hlog
  have hk2 := ArithmeticCorrespondencePositivity.re_weilTest_nonneg hf0 (-Real.log n - D)
  have : c * (u n / Real.sqrt n) ≤ (u n / Real.sqrt n) *
      (Tr D (EF.weilTest (cx f) (cx f)) (Real.log n)).re := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hk1 hwn
  refine this.trans (mul_le_mul_of_nonneg_left ?_ hwn)
  simp only [ArithmeticCastelnuovoSeveri.translate] at hk2 ⊢
  linarith

/-! ### Growth of the mass along the lags -/

/-- Integers in `[x, y]`: at least `y − x − 1` of them. -/
theorem le_card_Icc_ceil_floor {x y : ℝ} (hx : 0 ≤ x) :
    y - x - 1 ≤ ((Finset.Icc ⌈x⌉₊ ⌊y⌋₊).card : ℝ) := by
  rw [Nat.card_Icc]
  rcases le_or_gt ⌈x⌉₊ (⌊y⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h]
    push_cast
    have h1 := Nat.ceil_lt_add_one hx
    rcases le_or_gt 0 y with hy | hy
    · have h2 := Nat.lt_floor_add_one y
      linarith
    · have : ⌊y⌋₊ = 0 := Nat.floor_of_nonpos hy.le
      rw [this]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈x⌉₊]
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
    have h1 : (⌊y⌋₊ : ℝ) + 1 < ⌈x⌉₊ := by exact_mod_cast h
    have h2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
    rcases le_or_gt 0 y with hy | hy
    · have h3 := Nat.lt_floor_add_one y
      linarith
    · linarith

/-- `e^{δx} − B` exceeds every bound along `x = d log 2`. -/
theorem exists_nat_lt_exp {A δ B M R : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    ∃ d : ℕ, 1 ≤ d ∧ R < (d : ℝ) * Real.log 2 ∧
      M < A * Real.exp (δ * ((d : ℝ) * Real.log 2)) - B := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨d, hd⟩ := exists_nat_gt (max 1 (max (R / Real.log 2) ((M + B) / (A * δ * Real.log 2))))
  have hd1 : (1 : ℝ) < d := lt_of_le_of_lt (le_max_left _ _) hd
  have hdR : R / Real.log 2 < d := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hd
  have hdM : (M + B) / (A * δ * Real.log 2) < d :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hd
  refine ⟨d, by exact_mod_cast hd1.le, ?_, ?_⟩
  · rwa [div_lt_iff₀ hl] at hdR
  · have hexp := Real.add_one_le_exp (δ * ((d : ℝ) * Real.log 2))
    have hAδ : 0 < A * δ * Real.log 2 := by positivity
    rw [div_lt_iff₀ hAδ] at hdM
    nlinarith

/-- The window `[e^{D − r}, e^{D + r}]` of integers. -/
theorem mem_logWindow {D r : ℝ} (hDr : r < D) {n : ℕ}
    (hn : n ∈ Finset.Icc ⌈Real.exp (D - r)⌉₊ ⌊Real.exp (D + r)⌋₊) :
    2 ≤ n ∧ |Real.log n - D| ≤ r ∧ (n : ℝ) ≤ Real.exp (D + r) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  have hlo : Real.exp (D - r) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hhi : (n : ℝ) ≤ Real.exp (D + r) :=
    (Nat.cast_le.mpr h2).trans (Nat.floor_le (Real.exp_pos _).le)
  have hone : 1 < Real.exp (D - r) := Real.one_lt_exp_iff.mpr (by linarith)
  have hn2 : 2 ≤ n := by
    have : 1 < (n : ℝ) := lt_of_lt_of_le hone hlo
    have : 1 < n := by exact_mod_cast this
    omega
  have hnpos : (0 : ℝ) < n := by positivity
  refine ⟨hn2, abs_le.mpr ⟨?_, ?_⟩, hhi⟩
  · have := Real.log_le_log (Real.exp_pos _) hlo
    rw [Real.log_exp] at this; linarith
  · have := Real.log_le_log hnpos hhi
    rw [Real.log_exp] at this; linarith

/-! ### Brun–Titchmarsh and short-interval PNT do not decide the sign -/

/-- The perturbation `ε n^{−η}` changes the partial sums on `(a, b]` by at most `ε (b − a) a^{−η}`:
every statement on prime sums in intervals that tolerates a relative error `o(1)` holds for `λ` and
for `λ + ε n^{−η}` alike. -/
theorem sum_perturbation_Ioc_le (lam : ℕ → ℝ) {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) {a b : ℕ}
    (ha : 1 ≤ a) :
    0 ≤ ∑ n ∈ Finset.Ioc a b, (lam n + ε * (n : ℝ) ^ (-η)) - ∑ n ∈ Finset.Ioc a b, lam n ∧
      ∑ n ∈ Finset.Ioc a b, (lam n + ε * (n : ℝ) ^ (-η)) - ∑ n ∈ Finset.Ioc a b, lam n ≤
        ε * ((b : ℝ) - a) * (a : ℝ) ^ (-η) := by
  rw [Finset.sum_add_distrib, add_sub_cancel_left]
  refine ⟨Finset.sum_nonneg fun n _ => mul_nonneg hε (Real.rpow_nonneg (Nat.cast_nonneg _) _), ?_⟩
  have hterm : ∀ n ∈ Finset.Ioc a b, ε * (n : ℝ) ^ (-η) ≤ ε * (a : ℝ) ^ (-η) := by
    intro n hn
    have hna : a < n := (Finset.mem_Ioc.mp hn).1
    refine mul_le_mul_of_nonneg_left ?_ hε
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast ha) (by exact_mod_cast hna.le)
      (neg_nonpos.mpr hη)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  rcases le_or_gt a b with hab | hab
  · rw [Nat.cast_sub hab]; ring_nf; rfl
  · rw [Nat.sub_eq_zero_of_le hab.le, Nat.cast_zero, zero_mul]
    have hba : (b : ℝ) < a := by exact_mod_cast hab
    have : (b : ℝ) - a ≤ 0 := by linarith
    have hpos : 0 ≤ ε * (a : ℝ) ^ (-η) := mul_nonneg hε (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    nlinarith

/-- **`λ` and `λ + ε n^{−η}` are never both dyadic positive** along a nonnegative generator, for
`0 < η < 1/2`. The difference has dyadic mass `≥ c ε (1 − e^{−2r}) 2^{(1/2 − η)d} − cε`. -/
theorem not_dyadicPositive_and_perturbed (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 (cx f))
    (hfc : HasCompactSupport (cx f)) (hf0 : ∀ x, 0 ≤ f x) (hne : ∃ x, f x ≠ 0) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hη2 : η < 1 / 2) :
    ¬ (DyadicPositive lam (cx f) ∧
      DyadicPositive (fun n => lam n + ε * (n : ℝ) ^ (-η)) (cx f)) := by
  obtain ⟨r, hr, c, hc, hk⟩ := exists_re_weilTest_ge hf hfc hne
  refine not_dyadicPositive_and_of_unbounded hf0 hfc
    (fun n _ => le_add_of_nonneg_right (mul_nonneg hε.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    fun M => ?_
  set δ : ℝ := 1 / 2 - η
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hA : 0 < c * ε * (1 - Real.exp (-(2 * r))) := by
    have : Real.exp (-(2 * r)) < 1 := Real.exp_lt_one.mpr (by linarith)
    have : 0 < 1 - Real.exp (-(2 * r)) := by linarith
    positivity
  obtain ⟨d, hd1, hdr, hdM⟩ := exists_nat_lt_exp (B := c * ε) (M := M) (R := r) hA hδ
  refine ⟨d, hd1, lt_of_lt_of_le hdM ?_⟩
  set D : ℝ := (d : ℝ) * Real.log 2
  set W := Finset.Icc ⌈Real.exp (D - r)⌉₊ ⌊Real.exp (D + r)⌋₊
  have hu : ∀ n, 2 ≤ n → 0 ≤ lam n + ε * (n : ℝ) ^ (-η) - lam n := fun n _ => by
    rw [add_sub_cancel_left]; exact mul_nonneg hε.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hwin := primeMass_ge_window hu hf0 hfc hk D W fun n hn =>
    ⟨(mem_logWindow hdr hn).1, (mem_logWindow hdr hn).2.1⟩
  refine le_trans ?_ hwin
  -- each weight is at least `ε e^{−(1/2 + η)(D + r)}`
  have hlow : ∀ n ∈ W, ε * Real.exp (-(1 / 2 + η) * (D + r)) ≤
      (lam n + ε * (n : ℝ) ^ (-η) - lam n) / Real.sqrt n := by
    intro n hn
    obtain ⟨h2, -, hhi⟩ := mem_logWindow hdr hn
    have h2' : (2 : ℝ) ≤ n := by exact_mod_cast h2
    have hnpos : (0 : ℝ) < n := by linarith
    rw [add_sub_cancel_left, Real.sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_sub hnpos]
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    have e : Real.exp (-(1 / 2 + η) * (D + r)) = Real.exp (D + r) ^ (-η - 1 / 2) := by
      rw [← Real.exp_mul]; congr 1; ring
    rw [e]
    exact Real.rpow_le_rpow_of_nonpos hnpos hhi (by linarith)
  have hsum : (W.card : ℝ) * (ε * Real.exp (-(1 / 2 + η) * (D + r))) ≤
      ∑ n ∈ W, (lam n + ε * (n : ℝ) ^ (-η) - lam n) / Real.sqrt n := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]; exact Finset.sum_le_sum hlow
  have hcard := le_card_Icc_ceil_floor (x := Real.exp (D - r)) (y := Real.exp (D + r))
    (Real.exp_pos _).le
  -- the window count times the weight
  have hE : 0 ≤ ε * Real.exp (-(1 / 2 + η) * (D + r)) := by positivity
  have hmain : c * ε * (1 - Real.exp (-(2 * r))) * Real.exp (δ * D) - c * ε ≤
      c * ((Real.exp (D + r) - Real.exp (D - r) - 1) * (ε * Real.exp (-(1 / 2 + η) * (D + r)))) := by
    have e1 : Real.exp (D + r) * Real.exp (-(1 / 2 + η) * (D + r)) = Real.exp (δ * (D + r)) := by
      rw [← Real.exp_add]; congr 1; simp only [δ]; ring
    have e2 : Real.exp (D - r) * Real.exp (-(1 / 2 + η) * (D + r)) =
        Real.exp (δ * (D + r)) * Real.exp (-(2 * r)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; simp only [δ]; ring
    have e3 : Real.exp (δ * D) ≤ Real.exp (δ * (D + r)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have e4 : Real.exp (-(1 / 2 + η) * (D + r)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.log_pos one_lt_two])
    have h1e : 0 ≤ 1 - Real.exp (-(2 * r)) := by
      have : Real.exp (-(2 * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    have : (Real.exp (D + r) - Real.exp (D - r) - 1) * (ε * Real.exp (-(1 / 2 + η) * (D + r))) =
        ε * (Real.exp (δ * (D + r)) * (1 - Real.exp (-(2 * r))) -
          Real.exp (-(1 / 2 + η) * (D + r))) := by
      rw [show (Real.exp (D + r) - Real.exp (D - r) - 1) * (ε * Real.exp (-(1 / 2 + η) * (D + r)))
          = ε * (Real.exp (D + r) * Real.exp (-(1 / 2 + η) * (D + r)) -
            Real.exp (D - r) * Real.exp (-(1 / 2 + η) * (D + r)) -
              Real.exp (-(1 / 2 + η) * (D + r))) by ring, e1, e2]
      ring
    rw [this]
    have := mul_le_mul_of_nonneg_right e3 h1e
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ c * ε)]
  calc c * ε * (1 - Real.exp (-(2 * r))) * Real.exp (δ * D) - c * ε
      ≤ c * ((Real.exp (D + r) - Real.exp (D - r) - 1) *
          (ε * Real.exp (-(1 / 2 + η) * (D + r)))) := hmain
    _ ≤ c * ((W.card : ℝ) * (ε * Real.exp (-(1 / 2 + η) * (D + r)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hE) hc.le
    _ ≤ c * ∑ n ∈ W, (lam n + ε * (n : ℝ) ^ (-η) - lam n) / Real.sqrt n :=
        mul_le_mul_of_nonneg_left hsum hc.le

/-- **The von Mangoldt weight and its `n^{−η}` perturbation** share all interval statements up to
relative error `O(a^{−η})` (`sum_perturbation_Ioc_le`), yet at most one of them is dyadic positive
along any nonnegative generator. -/
theorem not_dyadicPositive_vonMangoldt_and_perturbed {f : ℝ → ℝ} (hf : ContDiff ℝ 2 (cx f))
    (hfc : HasCompactSupport (cx f)) (hf0 : ∀ x, 0 ≤ f x) (hne : ∃ x, f x ≠ 0) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hη2 : η < 1 / 2) :
    ¬ (DyadicPositive (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (cx f) ∧
      DyadicPositive (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + ε * (n : ℝ) ^ (-η))
        (cx f)) :=
  not_dyadicPositive_and_perturbed _ hf hfc hf0 hne hε hη hη2

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
