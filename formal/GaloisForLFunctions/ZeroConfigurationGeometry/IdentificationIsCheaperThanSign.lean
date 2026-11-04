import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold
import GaloisForLFunctions.SquareRootThreshold.OnLineShadowIndistinguishability
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDegreeFiltrationOfACurveIsItsWindowFiltration
import GaloisForLFunctions.HTGeometry.MultisetNewtonSolve
import GaloisForLFunctions.HTGeometry.MultisetSymmetricDetermination

/-!
# Identification is cheaper than sign: the function-field camera

A curve datum `D` (`ArithmeticCastelnuovoSeveri.CurveDatum`) is a Frobenius configuration: `2g`
normalized eigenvalues `β_i`, closed under conjugation and under `β ↦ β⁻¹`. Its zeros form `2g`
vertical columns of spacing `2π/log q`, and its image on windows of aperture `a` is
`W(f, f) = log q Σ_m (f ⋆ f̃)(m log q) t_{|m|}`, `t_m = Σ_i β_i^m` (`W_curveConfig_lagFormula`).
The camera of aperture `a` therefore reads exactly the traces `t_m` with `m log q < 2a`.

* **Identification** (`spectrum_eq_of_powerSum_eq`). If `∏ β_i = 1` (the sign of the functional
  equation of a curve), the first `g` traces determine the configuration: Newton's identities give
  `e_1, …, e_g`, and inversion symmetry gives `e_{2g−k} = e_k` (`esymm_spectrum_reflect`).
* **The camera identifies above `g log q`** (`spectrum_eq_of_weil_eq_on_aperture`). Equal images
  on all windows of one aperture `a > g log q / 2` force equal configurations. The two-bump window
  at lag `n log q` reads `2(t_0 − t_n)` (`W_lag_nat_mul_of_lagFormula`).
* **Certification at the identification threshold** (`pure_iff_of_weil_eq_on_aperture`). Above
  lag `g log q` equal images force equal purity, and purity is the position of the trace points
  `β + β⁻¹` in `[−2, 2]`. Below it the pure and golden root data share their images. So in the
  function-field model reality is certified sign-free exactly at the identification threshold.
* **Classification of mimic column clusters** (`curveConfig_weil_eq_iff_trace_eq`). Two curve data
  with the same `q` and the same number of points are mimics at aperture `a` exactly when
  `t_m = t'_m` for every lag `m log q < 2a`.
* **Sharpness: a pure configuration and a totally tilted one are mimics up to `g log q`**
  (`identification_threshold_sharp`). The roots of `x^{2g} + 1` (all on the unit circle) and of
  `x^{2g} − 3x^g + 1` (the `g`-th roots of `φ^{±2}`, none on the unit circle) have the same traces
  `t_1 = ⋯ = t_{g−1} = 0`, hence the same image on every window of aperture `a ≤ g log q / 2`.

Sign-based certification is proved at a larger aperture: Weil positivity at aperture `a` decides
purity once `a > (2g − 1) log q / 2` (`curveConfig_weil_nonneg_iff_unitary_of_card_le`), a window
of `2g` lags. The camera determines the configuration with `g` lags. Below lag `g log q` the golden
root datum is positive (it shares the image of the pure datum) although no point lies on the
circle, so positivity cannot decide purity there either.
-/

open Complex Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 ArithmeticCastelnuovoSeveri SquareRootThreshold _root_.RHTower

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-! ### Frobenius spectra -/

/-- The Frobenius spectrum of a curve datum, as a multiset. -/
def spectrum (D : CurveDatum ι) : Multiset ℂ := Finset.univ.val.map D.β

theorem card_spectrum (D : CurveDatum ι) : Multiset.card (spectrum D) = Fintype.card ι := by
  simp [spectrum]

theorem powerSum_eq_spectrum (D : CurveDatum ι) (j : ℕ) :
    D.powerSum j = ((spectrum D).map fun x => x ^ j).sum := by
  rw [spectrum, Multiset.map_map]; rfl

theorem CurveDatum.β_ne_zero (D : CurveDatum ι) (i : ι) : D.β i ≠ 0 := fun h => by
  have := D.β_fePerm i
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem esymm_spectrum_zero (D : CurveDatum ι) : (spectrum D).esymm 0 = 1 := by
  simp [spectrum, Finset.esymm_map_val]

/-- **Inversion symmetry of the coefficients.** If `∏ β_i = 1`, then `e_{N−k} = e_k`. -/
theorem esymm_spectrum_reflect [DecidableEq ι] (D : CurveDatum ι) (hprod : ∏ i, D.β i = 1)
    {k : ℕ} (hk : k ≤ Fintype.card ι) :
    (spectrum D).esymm (Fintype.card ι - k) = (spectrum D).esymm k := by
  -- reindex by the functional-equation permutation: `e_k(β) = e_k(β⁻¹)`
  have hperm : (Finset.univ.val.map fun i => D.β (D.fePerm i)) = spectrum D := by
    rw [spectrum, show (fun i => D.β (D.fePerm i)) = D.β ∘ D.fePerm from rfl, ← Multiset.map_map,
      show Multiset.map (⇑D.fePerm) Finset.univ.val =
        (Finset.univ.map D.fePerm.toEmbedding).val from rfl, Finset.map_univ_equiv]
  have hinv : ∀ i, D.β (D.fePerm i) = (D.β i)⁻¹ := fun i =>
    eq_inv_of_mul_eq_one_left (D.β_fePerm i)
  conv_rhs => rw [← hperm]
  rw [spectrum, Finset.esymm_map_val, Finset.esymm_map_val]
  simp_rw [hinv, Finset.prod_inv_distrib]
  refine (Finset.sum_nbij' (fun t => tᶜ) (fun t => tᶜ) ?_ ?_ ?_ ?_ ?_).symm
  · intro t ht
    simp only [Finset.mem_powersetCard] at ht ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_compl, ht.2]⟩
  · intro t ht
    simp only [Finset.mem_powersetCard] at ht ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_compl, ht.2]; omega⟩
  · intro t _; exact compl_compl t
  · intro t _; exact compl_compl t
  · intro t _
    have h := Finset.prod_sdiff (f := D.β) (Finset.subset_univ t)
    rw [hprod, ← Finset.compl_eq_univ_sdiff] at h
    exact (eq_inv_of_mul_eq_one_left h).symm

/-- **Identification from `g` traces.** Two Frobenius configurations with `2g` points, product
`1`, and equal power sums `t_1, …, t_g` are equal. -/
theorem spectrum_eq_of_powerSum_eq [DecidableEq ι] [DecidableEq ι'] (D : CurveDatum ι)
    (D' : CurveDatum ι') {g : ℕ} (hN : Fintype.card ι = 2 * g) (hN' : Fintype.card ι' = 2 * g)
    (hprod : ∏ i, D.β i = 1) (hprod' : ∏ i, D'.β i = 1)
    (hp : ∀ j, 1 ≤ j → j ≤ g → D.powerSum j = D'.powerSum j) : spectrum D = spectrum D' := by
  have hps : ∀ j, 1 ≤ j → j ≤ g →
      ((spectrum D).map fun x => x ^ j).sum = ((spectrum D').map fun x => x ^ j).sum :=
    fun j h1 h2 => by rw [← powerSum_eq_spectrum, ← powerSum_eq_spectrum, hp j h1 h2]
  -- Newton: the first `g` coefficients agree
  have hlow : ∀ k, k ≤ g → (spectrum D).esymm k = (spectrum D').esymm k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [esymm_spectrum_zero, esymm_spectrum_zero]
      rw [multiset_esymm_eq_of_powerSum _ k hk0, multiset_esymm_eq_of_powerSum _ k hk0,
        hps k hk0 hk]
      congr 2
      refine Finset.sum_congr rfl fun a ha => ?_
      simp only [Finset.mem_filter, Set.mem_Ioo] at ha
      have hsum : a.1 + a.2 = k := by simpa using ha.1
      rw [ih a.1 ha.2.2 (by omega), hps a.2 (by omega) (by omega)]
  have hcard : Multiset.card (spectrum D) = Multiset.card (spectrum D') := by
    rw [card_spectrum, card_spectrum, hN, hN']
  refine multiset_eq_of_esymm_eq hcard fun k hk => ?_
  rw [card_spectrum, hN] at hk
  by_cases hkg : k ≤ g
  · exact hlow k hkg
  · have h1 := esymm_spectrum_reflect D hprod (k := 2 * g - k) (by rw [hN]; omega)
    have h2 := esymm_spectrum_reflect D' hprod' (k := 2 * g - k) (by rw [hN']; omega)
    rw [hN, show 2 * g - (2 * g - k) = k by omega] at h1
    rw [hN', show 2 * g - (2 * g - k) = k by omega] at h2
    rw [h1, h2, hlow _ (by omega)]

/-! ### The camera identifies above `g log q` -/

theorem apertureWindow_twoBump {a w v : ℝ} (hw : 0 < w) (hv : 0 ≤ v) (hva : v / 2 + w ≤ a) :
    ApertureWindow a (twoBump (modScaledBump w 0) v (-1)) :=
  ⟨contDiff_bumpTest (contDiff_modScaledBump_two w 0) v _,
    (tsupport_twoBump_modScaledBump_subset hw hv).trans
      (Set.Icc_subset_Icc (by linarith) hva)⟩

/-- **The camera of aperture `a > g log q / 2` identifies Frobenius configurations.** -/
theorem spectrum_eq_of_weil_eq_on_aperture [DecidableEq ι] [DecidableEq ι'] (D : CurveDatum ι)
    (D' : CurveDatum ι') (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) (hD' : ∀ i, ‖D'.β i‖ ≤ D'.sqrtq)
    (hq : D.q = D'.q) {g : ℕ} (hN : Fintype.card ι = 2 * g) (hN' : Fintype.card ι' = 2 * g)
    (hprod : ∏ i, D.β i = 1) (hprod' : ∏ i, D'.β i = 1) {a : ℝ}
    (ha : (g : ℝ) * Real.log D.q < 2 * a)
    (hW : ∀ f, ApertureWindow a f → (D.curveConfig hD).W f f = (D'.curveConfig hD').W f f) :
    spectrum D = spectrum D' := by
  set ℓ := Real.log D.q with hℓ
  have hℓ0 : 0 < ℓ := D.log_q_pos
  refine spectrum_eq_of_powerSum_eq D D' hN hN' hprod hprod' fun j hj1 hjg => ?_
  set w := min ((2 * a - g * ℓ) / 4) (ℓ / 8) with hw
  have hw0 : 0 < w := lt_min (by linarith) (by positivity)
  have hwℓ : 4 * w < ℓ := by
    have := min_le_right ((2 * a - g * ℓ) / 4) (ℓ / 8); linarith
  have hjℓ : (j : ℝ) * ℓ ≤ g * ℓ := mul_le_mul_of_nonneg_right (by exact_mod_cast hjg) hℓ0.le
  have hwin : ApertureWindow a (twoBump (modScaledBump w 0) (j * ℓ) (-1)) :=
    apertureWindow_twoBump hw0 (by positivity) (by
      have := min_le_left ((2 * a - g * ℓ) / 4) (ℓ / 8); linarith)
  have h := hW _ hwin
  have hl : D'.q = D.q := hq.symm
  rw [W_lag_nat_mul_of_lagFormula (D.curveConfig hD) (fun m : ℤ => (D.trace m.natAbs : ℂ))
      (fun f hf hfc => D.W_curveConfig_lagFormula hD hf hfc) hw0 hwℓ hj1,
    W_lag_nat_mul_of_lagFormula (ℓ := ℓ) (D'.curveConfig hD') (fun m : ℤ => (D'.trace m.natAbs : ℂ))
      (fun f hf hfc => by rw [hℓ, hq]; exact D'.W_curveConfig_lagFormula hD' hf hfc) hw0 hwℓ hj1]
    at h
  have hκ := integral_norm_sq_modScaledBump_pos hw0
  have hne : ((ℓ : ℝ) : ℂ) * (((∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_mul]; exact_mod_cast (mul_pos hℓ0 hκ).ne'
  have h2 := mul_left_cancel₀ hne h
  simp only [Int.natAbs_zero, Int.natAbs_neg, Int.natAbs_natCast, CurveDatum.trace_zero,
    hN, hN'] at h2
  rw [D.powerSum_eq_trace, D'.powerSum_eq_trace]
  linear_combination (-1 / 2 : ℂ) * h2

/-! ### Certification at the identification threshold -/

theorem pure_iff_spectrum (D : CurveDatum ι) :
    (∀ i, ‖D.β i‖ = 1) ↔ ∀ β ∈ spectrum D, ‖β‖ = 1 := by
  simp [spectrum]

/-- **Purity is a function of the first `g` traces.** Two Frobenius configurations with `2g` points,
product `1` and equal `t_1, …, t_g` are pure together. -/
theorem pure_iff_of_powerSum_eq [DecidableEq ι] [DecidableEq ι'] (D : CurveDatum ι)
    (D' : CurveDatum ι') {g : ℕ} (hN : Fintype.card ι = 2 * g) (hN' : Fintype.card ι' = 2 * g)
    (hprod : ∏ i, D.β i = 1) (hprod' : ∏ i, D'.β i = 1)
    (hp : ∀ j, 1 ≤ j → j ≤ g → D.powerSum j = D'.powerSum j) :
    (∀ i, ‖D.β i‖ = 1) ↔ ∀ i, ‖D'.β i‖ = 1 := by
  rw [pure_iff_spectrum, pure_iff_spectrum, spectrum_eq_of_powerSum_eq D D' hN hN' hprod hprod' hp]

/-- **The camera of aperture `a > g log q / 2` certifies purity.** Equal images force equal purity,
and purity is the position of the trace points in `[−2, 2]`
(`curveDatum_pure_iff_tracePoints`): no sign of a form enters. Below the threshold the pure and
golden root data share their images (`identification_threshold_sharp`). -/
theorem pure_iff_of_weil_eq_on_aperture [DecidableEq ι] [DecidableEq ι'] (D : CurveDatum ι)
    (D' : CurveDatum ι') (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) (hD' : ∀ i, ‖D'.β i‖ ≤ D'.sqrtq)
    (hq : D.q = D'.q) {g : ℕ} (hN : Fintype.card ι = 2 * g) (hN' : Fintype.card ι' = 2 * g)
    (hprod : ∏ i, D.β i = 1) (hprod' : ∏ i, D'.β i = 1) {a : ℝ}
    (ha : (g : ℝ) * Real.log D.q < 2 * a)
    (hW : ∀ f, ApertureWindow a f → (D.curveConfig hD).W f f = (D'.curveConfig hD').W f f) :
    (∀ i, ‖D.β i‖ = 1) ↔ ∀ i, ‖D'.β i‖ = 1 := by
  rw [pure_iff_spectrum, pure_iff_spectrum,
    spectrum_eq_of_weil_eq_on_aperture D D' hD hD' hq hN hN' hprod hprod' ha hW]

/-! ### Classification of mimic column clusters -/

/-- **Mimic column clusters are exactly those with equal low traces.** Two curve data with the same
field size and the same number of points have the same image on every window of aperture `a`
exactly when their traces `t_m` agree for every lag `m log q < 2a`. -/
theorem curveConfig_weil_eq_iff_trace_eq (D : CurveDatum ι) (D' : CurveDatum ι')
    (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) (hD' : ∀ i, ‖D'.β i‖ ≤ D'.sqrtq) (hq : D.q = D'.q)
    (hN : Fintype.card ι = Fintype.card ι') (a : ℝ) :
    (∀ f, ApertureWindow a f → (D.curveConfig hD).W f f = (D'.curveConfig hD').W f f) ↔
      ∀ m : ℕ, 1 ≤ m → (m : ℝ) * Real.log D.q < 2 * a → D.trace m = D'.trace m := by
  set ℓ := Real.log D.q with hℓ
  have hℓ0 : 0 < ℓ := D.log_q_pos
  have hlag' : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (D'.curveConfig hD').W f f = ((ℓ : ℝ) : ℂ) *
        ∑' m : ℤ, EF.weilTest f f (m * ℓ) * (D'.trace m.natAbs : ℂ) := fun f hf hfc => by
    rw [hℓ, hq]; exact D'.W_curveConfig_lagFormula hD' hf hfc
  constructor
  · intro hW m hm1 hm
    set w := min ((2 * a - m * ℓ) / 4) (ℓ / 8) with hw
    have hw0 : 0 < w := lt_min (by linarith) (by positivity)
    have hwℓ : 4 * w < ℓ := by
      have := min_le_right ((2 * a - m * ℓ) / 4) (ℓ / 8); linarith
    have hwin : ApertureWindow a (twoBump (modScaledBump w 0) (m * ℓ) (-1)) :=
      apertureWindow_twoBump hw0 (by positivity) (by
        have := min_le_left ((2 * a - m * ℓ) / 4) (ℓ / 8); linarith)
    have h := hW _ hwin
    rw [W_lag_nat_mul_of_lagFormula (D.curveConfig hD) (fun m : ℤ => (D.trace m.natAbs : ℂ))
        (fun f hf hfc => D.W_curveConfig_lagFormula hD hf hfc) hw0 hwℓ hm1,
      W_lag_nat_mul_of_lagFormula (ℓ := ℓ) (D'.curveConfig hD')
        (fun m : ℤ => (D'.trace m.natAbs : ℂ)) hlag' hw0 hwℓ hm1] at h
    have hκ := integral_norm_sq_modScaledBump_pos hw0
    have hne : ((ℓ : ℝ) : ℂ) * (((∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_mul]; exact_mod_cast (mul_pos hℓ0 hκ).ne'
    have h2 := mul_left_cancel₀ hne h
    simp only [Int.natAbs_zero, Int.natAbs_neg, Int.natAbs_natCast, CurveDatum.trace_zero,
      hN] at h2
    have h3 : (D.trace m : ℂ) = D'.trace m := by linear_combination (-1 / 2 : ℂ) * h2
    exact_mod_cast h3
  · intro htr f hf
    have hfc := hf.hasCompactSupport
    rw [D.W_curveConfig_lagFormula hD hf.1 hfc, hlag' f hf.1 hfc]
    congr 1
    refine tsum_congr fun m => ?_
    by_cases hm : 2 * a ≤ (m.natAbs : ℝ) * ℓ
    · have hv : 2 * a ≤ |(m : ℝ) * ℓ| := by
        rw [abs_mul, abs_of_pos hℓ0]; rwa [Nat.cast_natAbs, Int.cast_abs] at hm
      rw [weilTest_eq_zero_of_two_mul_le hf.1.continuous hf.2 hv, zero_mul, zero_mul]
    · replace hm := not_le.mp hm
      congr 1
      rcases Nat.eq_zero_or_pos m.natAbs with h0 | h0
      · rw [h0, CurveDatum.trace_zero, CurveDatum.trace_zero, hN]
      · rw [htr m.natAbs h0 hm]

/-! ### Two mimics: the pure datum and the golden root -/

/-- `ω = e^{2πi/g}`. -/
def unitRoot (g : ℕ) : ℂ := cexp (2 * π * I / g)

/-- The point `r^{±1} ω^k`, `(±, k) ∈ Bool × Fin g`. -/
def rootPoint (g : ℕ) (r : ℂ) (p : Bool × Fin g) : ℂ :=
  (if p.1 then r else r⁻¹) * unitRoot g ^ (p.2 : ℕ)

/-- `(s, k) ↦ (¬s, −k)`. -/
def flipNeg (g : ℕ) [NeZero g] : Equiv.Perm (Bool × Fin g) :=
  Equiv.prodCongr (Function.Involutive.toPerm _ Bool.not_not) (Equiv.neg (Fin g))

/-- `(s, k) ↦ (s, −k)`. -/
def negOnly (g : ℕ) [NeZero g] : Equiv.Perm (Bool × Fin g) :=
  Equiv.prodCongr (Equiv.refl Bool) (Equiv.neg (Fin g))

variable {g : ℕ} [NeZero g]

theorem unitRoot_pow_card : unitRoot g ^ g = 1 := by
  rw [unitRoot, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  exact ⟨1, by field_simp [(NeZero.ne g : g ≠ 0)]; push_cast; ring⟩

omit [NeZero g] in
theorem unitRoot_ne_zero : unitRoot g ≠ 0 := Complex.exp_ne_zero _

theorem unitRoot_pow_neg (k : Fin g) :
    unitRoot g ^ ((-k : Fin g) : ℕ) = (unitRoot g ^ (k : ℕ))⁻¹ := by
  rw [Fin.val_neg', ← pow_eq_pow_mod _ unitRoot_pow_card]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add, Nat.sub_add_cancel k.isLt.le, unitRoot_pow_card]

omit [NeZero g] in
theorem conj_unitRoot : conj (unitRoot g) = (unitRoot g)⁻¹ := by
  rw [unitRoot, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]; ring

omit [NeZero g] in
theorem norm_unitRoot : ‖unitRoot g‖ = 1 := by
  rw [unitRoot, show 2 * (π : ℂ) * I / g = ((2 * π / g : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem unitRoot_pow_ne_one {j : ℕ} (hj1 : 1 ≤ j) (hjg : j < g) : unitRoot g ^ j ≠ 1 := by
  rw [unitRoot, ← Complex.exp_nat_mul]
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hg0 : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
  have hpi : (2 * π : ℂ) * I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hjn : (j : ℂ) = n * g := by
    have := hn
    field_simp at this
    linear_combination this
  have hjn' : (j : ℤ) = n * g := by exact_mod_cast hjn
  rcases lt_trichotomy n 0 with hn0 | rfl | hn0
  · have : (n : ℤ) * g < 0 := mul_neg_of_neg_of_pos hn0 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g))
    omega
  · omega
  · have : (g : ℤ) ≤ n * g := le_mul_of_one_le_left (by positivity) hn0
    omega

theorem sum_unitRoot_pow {j : ℕ} (hj1 : 1 ≤ j) (hjg : j < g) :
    ∑ k : Fin g, (unitRoot g ^ (k : ℕ)) ^ j = 0 := by
  simp_rw [← pow_mul, mul_comm _ j, pow_mul]
  rw [Fin.sum_univ_eq_sum_range (fun k => (unitRoot g ^ j) ^ k) g,
    geom_sum_eq (unitRoot_pow_ne_one hj1 hjg), ← pow_mul, mul_comm, pow_mul, unitRoot_pow_card,
    one_pow, sub_self, zero_div]

/-- The power sums `Σ (r^{±1}ω^k)^j` vanish for `1 ≤ j < g`. -/
theorem sum_rootPoint_pow (r : ℂ) {j : ℕ} (hj1 : 1 ≤ j) (hjg : j < g) :
    ∑ p : Bool × Fin g, rootPoint g r p ^ j = 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [rootPoint, if_true, Bool.false_eq_true, if_false, mul_pow, ← Finset.mul_sum,
    sum_unitRoot_pow hj1 hjg, mul_zero, add_zero]

theorem rootPoint_flipNeg_mul {r : ℂ} (hr : r ≠ 0) (p : Bool × Fin g) :
    rootPoint g r (flipNeg g p) * rootPoint g r p = 1 := by
  obtain ⟨s, k⟩ := p
  simp only [rootPoint, flipNeg, Equiv.prodCongr_apply, Prod.map, Function.Involutive.coe_toPerm,
    Equiv.neg_apply, unitRoot_pow_neg]
  have hk : unitRoot g ^ (k : ℕ) ≠ 0 := pow_ne_zero _ unitRoot_ne_zero
  cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
    field_simp

/-- `e^{iπ/2g}`: the pure datum is `{x : x^{2g} = −1}`. -/
def pureRadius (g : ℕ) : ℂ := cexp (π * I / (2 * g))

omit [NeZero g] in
theorem norm_pureRadius : ‖pureRadius g‖ = 1 := by
  rw [pureRadius, show (π : ℂ) * I / (2 * g) = ((π / (2 * g) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

omit [NeZero g] in
theorem conj_pureRadius : conj (pureRadius g) = (pureRadius g)⁻¹ := by
  rw [pureRadius, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]; ring

/-- The **pure datum**: the `2g` roots of `x^{2g} + 1`, all on the unit circle. -/
def pureDatum (g : ℕ) [NeZero g] (q : ℝ) (hq : 1 < q) : CurveDatum (Bool × Fin g) where
  q := q
  one_lt_q := hq
  β := rootPoint g (pureRadius g)
  conjPerm := flipNeg g
  β_conjPerm := fun ⟨s, k⟩ => by
    simp only [rootPoint, flipNeg, Equiv.prodCongr_apply, Prod.map,
      Function.Involutive.coe_toPerm, Equiv.neg_apply, unitRoot_pow_neg, map_mul, map_pow,
      conj_unitRoot, inv_pow]
    cases s <;> simp [conj_pureRadius, map_inv₀]
  fePerm := flipNeg g
  β_fePerm := rootPoint_flipNeg_mul (Complex.exp_ne_zero _)

/-- `φ^{2/g}`. -/
def goldenRadius (g : ℕ) : ℝ := Real.goldenRatio ^ ((2 : ℝ) / g)

omit [NeZero g] in
theorem goldenRadius_pos : 0 < goldenRadius g := Real.rpow_pos_of_pos Real.goldenRatio_pos _

theorem one_lt_goldenRadius : 1 < goldenRadius g :=
  Real.one_lt_rpow Real.one_lt_goldenRatio (by
    have : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
    positivity)

/-- The **golden root datum**: the `g`-th roots of `φ^{±2}`, the roots of `x^{2g} − 3x^g + 1`.
No point lies on the unit circle. -/
def goldenRootDatum (g : ℕ) [NeZero g] (q : ℝ) (hq : 1 < q) : CurveDatum (Bool × Fin g) where
  q := q
  one_lt_q := hq
  β := rootPoint g (goldenRadius g : ℂ)
  conjPerm := negOnly g
  β_conjPerm := fun ⟨s, k⟩ => by
    simp only [rootPoint, negOnly, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      Equiv.neg_apply, unitRoot_pow_neg, map_mul, map_pow, conj_unitRoot, inv_pow]
    cases s <;> simp [Complex.conj_ofReal, map_inv₀]
  fePerm := flipNeg g
  β_fePerm := rootPoint_flipNeg_mul (Complex.ofReal_ne_zero.mpr goldenRadius_pos.ne')

omit [NeZero g] in
theorem norm_rootPoint (r : ℂ) (p : Bool × Fin g) :
    ‖rootPoint g r p‖ = if p.1 then ‖r‖ else ‖r‖⁻¹ := by
  rw [rootPoint, norm_mul, norm_pow, norm_unitRoot, one_pow, mul_one]
  split_ifs <;> simp

theorem trace_rootPoint_eq_zero {D : CurveDatum (Bool × Fin g)} {r : ℂ} (hD : D.β = rootPoint g r)
    {j : ℕ} (hj1 : 1 ≤ j) (hjg : j < g) : D.trace j = 0 := by
  rw [CurveDatum.trace, CurveDatum.powerSum, hD, sum_rootPoint_pow r hj1 hjg, Complex.zero_re]

/-- **The identification threshold is sharp.** For `φ⁴ ≤ q`, the pure datum (every point on the
unit circle) and the golden root datum (no point on the unit circle) have the same image on every
window of aperture `a ≤ g log q / 2`. -/
theorem identification_threshold_sharp (q : ℝ) (hq : Real.goldenRatio ^ 4 ≤ q) :
    ∃ (hq1 : 1 < q) (hP : ∀ p, ‖(pureDatum g q hq1).β p‖ ≤ (pureDatum g q hq1).sqrtq)
      (hG : ∀ p, ‖(goldenRootDatum g q hq1).β p‖ ≤ (goldenRootDatum g q hq1).sqrtq),
      (∀ p, ‖(pureDatum g q hq1).β p‖ = 1) ∧ (∀ p, ‖(goldenRootDatum g q hq1).β p‖ ≠ 1) ∧
      ∀ a : ℝ, 2 * a ≤ g * Real.log q → ∀ f, ApertureWindow a f →
        ((pureDatum g q hq1).curveConfig hP).W f f =
          ((goldenRootDatum g q hq1).curveConfig hG).W f f := by
  have hφ4 : 1 < Real.goldenRatio ^ 4 := one_lt_pow₀ Real.one_lt_goldenRatio (by norm_num)
  have hq1 : 1 < q := hφ4.trans_le hq
  have hsq : 1 ≤ Real.sqrt q := by rw [Real.one_le_sqrt]; exact hq1.le
  have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
  have hrad : goldenRadius g ≤ Real.sqrt q := by
    rw [Real.le_sqrt goldenRadius_pos.le (by linarith), goldenRadius, ← Real.rpow_natCast,
      ← Real.rpow_mul Real.goldenRatio_pos.le]
    refine le_trans ?_ hq
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le Real.one_lt_goldenRatio.le ?_
    have : (1 : ℝ) ≤ g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
    rw [div_mul_eq_mul_div]; push_cast
    rw [div_le_iff₀ hg0]; nlinarith
  have hP : ∀ p, ‖(pureDatum g q hq1).β p‖ ≤ (pureDatum g q hq1).sqrtq := fun p => by
    change ‖rootPoint g (pureRadius g) p‖ ≤ Real.sqrt q
    rw [norm_rootPoint, norm_pureRadius, inv_one, ite_self]; exact hsq
  have hG : ∀ p, ‖(goldenRootDatum g q hq1).β p‖ ≤ (goldenRootDatum g q hq1).sqrtq := fun p => by
    change ‖rootPoint g (goldenRadius g : ℂ) p‖ ≤ Real.sqrt q
    rw [norm_rootPoint, Complex.norm_real, Real.norm_eq_abs, abs_of_pos goldenRadius_pos]
    split_ifs
    · exact hrad
    · exact (inv_le_one_of_one_le₀ one_lt_goldenRadius.le).trans hsq
  refine ⟨hq1, hP, hG, fun p => ?_, fun p => ?_, fun a ha f hf => ?_⟩
  · change ‖rootPoint g (pureRadius g) p‖ = 1
    rw [norm_rootPoint, norm_pureRadius, inv_one, ite_self]
  · change ‖rootPoint g (goldenRadius g : ℂ) p‖ ≠ 1
    rw [norm_rootPoint, Complex.norm_real, Real.norm_eq_abs, abs_of_pos goldenRadius_pos]
    split_ifs
    · exact one_lt_goldenRadius.ne'
    · exact (inv_lt_one_of_one_lt₀ one_lt_goldenRadius).ne
  · have hfc := hf.hasCompactSupport
    rw [(pureDatum g q hq1).W_curveConfig_lagFormula hP hf.1 hfc,
      (goldenRootDatum g q hq1).W_curveConfig_lagFormula hG hf.1 hfc]
    rw [show (pureDatum g q hq1).q = q from rfl, show (goldenRootDatum g q hq1).q = q from rfl]
    congr 1
    refine tsum_congr fun m => ?_
    by_cases hm : g ≤ m.natAbs
    · have hlq : 0 < Real.log q := Real.log_pos hq1
      have hv : 2 * a ≤ |(m : ℝ) * Real.log q| := by
        rw [abs_mul, abs_of_pos hlq]
        calc 2 * a ≤ g * Real.log q := ha
          _ ≤ |(m : ℝ)| * Real.log q := by
            refine mul_le_mul_of_nonneg_right ?_ hlq.le
            rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hm
      rw [weilTest_eq_zero_of_two_mul_le hf.1.continuous hf.2 hv, zero_mul, zero_mul]
    · replace hm := not_le.mp hm
      congr 1
      rcases Nat.eq_zero_or_pos m.natAbs with h0 | h0
      · rw [h0, CurveDatum.trace_zero, CurveDatum.trace_zero]
      · rw [trace_rootPoint_eq_zero (D := pureDatum g q hq1) rfl h0 hm,
          trace_rootPoint_eq_zero (D := goldenRootDatum g q hq1) rfl h0 hm]

end GaloisForLFunctions.ZeroConfigurationGeometry
