import GaloisForLFunctions.RHTower.MontgomeryDominantBandIsolation
import GaloisForLFunctions.RHTower.MontgomerySingleBandWide

/-!
# Several bands and the dominant-band law for wide bands

The multi-band window bound and the dominant-band isolation law with real-part bands of any width
`τ/log T`, using the damped Montgomery–Vaughan inequality in place of the Taylor band lemma.  The
lower constant of the dominant band is `mvWideBandConstant ℓ₀ D τ = ℓ₀e^{−2τℓ₀} − 26/(πD) − 9τ/(π²D²)`
and the upper constant of every other band is
`mvWideBandUpperConstant a ℓ D τ = e^{2τ(a+ℓ)} (ℓ + 26/(πD) + 9τ/(π²D²))`.  The hypotheses
`τ ≤ 1` and `a + ℓ ≤ 1` of the narrow-band versions are no longer needed.
-/

open Complex MeasureTheory Set Finset Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The wide-band upper constant `e^{2τ(a+ℓ)} (ℓ + 26/(πD) + 9τ/(π²D²))`. -/
def mvWideBandUpperConstant (a ℓ D τ : ℝ) : ℝ :=
  Real.exp (2 * τ * (a + ℓ)) * (ℓ + 26 / (Real.pi * D) + 9 * τ / (Real.pi ^ 2 * D ^ 2))

theorem mvWideBandUpperConstant_nonneg {a ℓ D τ : ℝ} (hℓ : 0 ≤ ℓ) (hD : 0 < D) (hτ : 0 ≤ τ) :
    0 ≤ mvWideBandUpperConstant a ℓ D τ := by
  unfold mvWideBandUpperConstant
  positivity

/-- Lower bound for one wide band's inner scale integral. -/
theorem band_inner_ge_wide (A : Finset XiZeroCopy) {T σ D a ℓ ℓ₀ τ : ℝ} (hT : 1 < T)
    (hD : 0 < D) (hℓ₀ : 0 ≤ ℓ₀) (hℓ : ℓ₀ ≤ ℓ) (ha : 0 ≤ a) (hτ0 : 0 ≤ τ)
    (hband : ∀ j ∈ A, σ ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ + τ / Real.log T)
    (hsep : ∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|)
    (hc : 0 ≤ mvWideBandConstant ℓ₀ D τ) {ξ : ℝ} (hξ : ξ ∈ Icc (-1 : ℝ) 1) :
    mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * A.card)
      ≤ ∫ α in a..a + ℓ, ‖GaloisForLFunctions.HTGeometry.mvBandSum (fun j : A => bandFreq T j)
          (fun j : A => bandCoeff ξ j) (fun j : A => bandTheta T σ j) α‖ ^ 2 := by
  classical
  have hL : 0 < Real.log T := Real.log_pos hT
  set u : A → ℝ := fun j => bandFreq T j with hu
  set d : A → ℂ := fun j => bandCoeff ξ j with hd
  set θ : A → ℝ := fun j => bandTheta T σ j with hθ
  have hθb : ∀ r : A, τ - τ ≤ θ r ∧ θ r ≤ τ := by
    intro r
    obtain ⟨h1, h2⟩ := hband r.1 r.2
    simp only [hθ, bandTheta]
    constructor
    · rw [sub_self]
      exact mul_nonneg (by linarith) hL.le
    · have h3 : ((r.1).1 : ℂ).re - σ ≤ τ / Real.log T := by linarith
      calc (((r.1).1 : ℂ).re - σ) * Real.log T ≤ (τ / Real.log T) * Real.log T := by gcongr
        _ = τ := by field_simp
  have hθnn : ∀ r : A, 0 ≤ θ r := fun r => by
    have := (hθb r).1
    rwa [sub_self] at this
  have hsep' : ∀ r s : A, r ≠ s → D ≤ |u r - u s| := by
    intro r s hrs
    exact hsep r.1 r.2 s.1 s.2 (fun h => hrs (Subtype.ext h))
  have h := GaloisForLFunctions.HTGeometry.interval_integral_normSq_mvBandSum_ge_band
    u d θ (a := a) hD hℓ₀ hℓ hτ0 hτ0 hθb hsep'
  have hcoef : Real.exp (-1) * A.card ≤ ∑ r : A, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) := by
    have hξ1 : |ξ| ≤ 1 := by rw [abs_le]; exact ⟨hξ.1, hξ.2⟩
    have : ∀ r : A, Real.exp (-1) ≤ ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) := by
      intro r
      have h1 : Real.exp (-1) ≤ ‖d r‖ ^ 2 := by
        refine le_trans ?_ (normSq_bandCoeff_ge ξ r.1)
        apply Real.exp_le_exp.mpr
        linarith
      have h2 : 1 ≤ Real.exp (2 * θ r * a) := by
        rw [← Real.exp_zero, Real.exp_le_exp]
        have := hθnn r
        positivity
      calc Real.exp (-1) = Real.exp (-1) * 1 := by ring
        _ ≤ ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) := mul_le_mul h1 h2 zero_le_one (by positivity)
    calc Real.exp (-1) * A.card = ∑ _r : A, Real.exp (-1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun r _ => this r
  calc mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * A.card)
      ≤ mvWideBandConstant ℓ₀ D τ * ∑ r : A, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) :=
        mul_le_mul_of_nonneg_left hcoef hc
    _ ≤ _ := by
        unfold mvWideBandConstant
        exact h

/-- Upper bound for one wide band's inner scale integral. -/
theorem band_inner_le_wide (A : Finset XiZeroCopy) {T σ D a ℓ τ : ℝ} (hT : 1 < T)
    (hD : 0 < D) (hℓ : 0 ≤ ℓ) (ha : 0 ≤ a) (hτ0 : 0 ≤ τ)
    (hband : ∀ j ∈ A, σ ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ + τ / Real.log T)
    (hsep : ∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|)
    {ξ : ℝ} (hξ : ξ ∈ Icc (-1 : ℝ) 1) :
    (∫ α in a..a + ℓ, ‖GaloisForLFunctions.HTGeometry.mvBandSum (fun j : A => bandFreq T j)
          (fun j : A => bandCoeff ξ j) (fun j : A => bandTheta T σ j) α‖ ^ 2)
      ≤ mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * A.card) := by
  classical
  have hL : 0 < Real.log T := Real.log_pos hT
  set u : A → ℝ := fun j => bandFreq T j with hu
  set d : A → ℂ := fun j => bandCoeff ξ j with hd
  set θ : A → ℝ := fun j => bandTheta T σ j with hθ
  have hθb : ∀ r : A, τ - τ ≤ θ r ∧ θ r ≤ τ := by
    intro r
    obtain ⟨h1, h2⟩ := hband r.1 r.2
    simp only [hθ, bandTheta]
    constructor
    · rw [sub_self]
      exact mul_nonneg (by linarith) hL.le
    · have h3 : ((r.1).1 : ℂ).re - σ ≤ τ / Real.log T := by linarith
      calc (((r.1).1 : ℂ).re - σ) * Real.log T ≤ (τ / Real.log T) * Real.log T := by gcongr
        _ = τ := by field_simp
  have hsep' : ∀ r s : A, r ≠ s → D ≤ |u r - u s| := by
    intro r s hrs
    exact hsep r.1 r.2 s.1 s.2 (fun h => hrs (Subtype.ext h))
  have h := GaloisForLFunctions.HTGeometry.interval_integral_normSq_mvBandSum_le_band
    u d θ (a := a) hD hℓ hτ0 hτ0 hθb hsep'
  have hcoef : ∑ r : A, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a)
      ≤ Real.exp (2 * τ * a) * (Real.exp 1 * A.card) := by
    have hξ1 : |ξ| ≤ 1 := by rw [abs_le]; exact ⟨hξ.1, hξ.2⟩
    have : ∀ r : A, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) ≤ Real.exp 1 * Real.exp (2 * τ * a) := by
      intro r
      have h1 : ‖d r‖ ^ 2 ≤ Real.exp 1 := (normSq_bandCoeff_le ξ r.1).trans (Real.exp_le_exp.mpr hξ1)
      have h2 : Real.exp (2 * θ r * a) ≤ Real.exp (2 * τ * a) := by
        rw [Real.exp_le_exp]
        have := (hθb r).2
        nlinarith
      exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
    calc ∑ r : A, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a)
        ≤ ∑ _r : A, Real.exp 1 * Real.exp (2 * τ * a) := Finset.sum_le_sum fun r _ => this r
      _ = Real.exp (2 * τ * a) * (Real.exp 1 * A.card) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          ring
  have hK0 : 0 ≤ Real.exp (2 * τ * ℓ) * (ℓ + 26 / (Real.pi * D) + 9 * τ / (Real.pi ^ 2 * D ^ 2)) := by
    positivity
  calc _ ≤ Real.exp (2 * τ * ℓ) * (ℓ + 26 / (Real.pi * D) + 9 * τ / (Real.pi ^ 2 * D ^ 2)) *
        ∑ r : A, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) := h
    _ ≤ Real.exp (2 * τ * ℓ) * (ℓ + 26 / (Real.pi * D) + 9 * τ / (Real.pi ^ 2 * D ^ 2)) *
        (Real.exp (2 * τ * a) * (Real.exp 1 * A.card)) := mul_le_mul_of_nonneg_left hcoef hK0
    _ = mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * A.card) := by
        unfold mvWideBandUpperConstant
        rw [show 2 * τ * (a + ℓ) = 2 * τ * ℓ + 2 * τ * a by ring, Real.exp_add]
        ring

/-- **Several wide bands, inner scale integral, flattened at `i₀`.** -/
theorem multiBand_inner_ge_wide {κ : Type} [Fintype κ] [DecidableEq κ] (A : κ → Finset XiZeroCopy)
    (hdisj : (Set.univ : Set κ).PairwiseDisjoint A) (σ : κ → ℝ) (i₀ : κ)
    {T D a ℓ ℓ₀ τ : ℝ} (hT : 1 < T) (hD : 0 < D) (hℓ₀ : 0 ≤ ℓ₀) (hℓ₀ℓ : ℓ₀ ≤ ℓ) (ha : 0 ≤ a)
    (hτ0 : 0 ≤ τ) (hσ : 1 / 2 ≤ σ i₀)
    (hband : ∀ i, ∀ j ∈ A i, σ i ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ i + τ / Real.log T)
    (hsep : ∀ j ∈ Finset.univ.biUnion A, ∀ k ∈ Finset.univ.biUnion A, j ≠ k →
      D ≤ |bandFreq T j - bandFreq T k|)
    (hc : 0 ≤ mvWideBandConstant ℓ₀ D τ) {ξ : ℝ} (hξ : ξ ∈ Icc (-1 : ℝ) 1) :
    Real.exp (2 * (a * (σ i₀ - 1 / 2) * Real.log T)) *
      (1 / 2 * (mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * (A i₀).card))
        - (Fintype.card κ : ℝ) * ∑ i ∈ Finset.univ.erase i₀,
            bandScalarSq T a (a + ℓ) (σ i₀) (σ i) *
              (mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * (A i).card)))
      ≤ ∫ α in a..a + ℓ, ‖zeroPowerSum (Finset.univ.biUnion A) (fun q : XiZeroCopy => (q.1 : ℂ))
          (T ^ α * Real.exp (-ξ))‖ ^ 2 := by
  classical
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hℓ : 0 ≤ ℓ := le_trans hℓ₀ hℓ₀ℓ
  set b := a + ℓ with hb
  have hab' : a ≤ b := by rw [hb]; linarith
  set L := Real.log T with hLdef
  -- band sums and amplitudes
  set B : κ → ℝ → ℂ := fun i α => GaloisForLFunctions.HTGeometry.mvBandSum
    (fun j : A i => bandFreq T j) (fun j : A i => bandCoeff ξ j) (fun j : A i => bandTheta T (σ i) j) α
    with hBdef
  set E : κ → ℝ → ℝ := fun i α => Real.exp (α * (σ i - 1 / 2) * L) with hEdef
  have hE0 : ∀ i α, 0 < E i α := fun i α => Real.exp_pos _
  have hdecomp : ∀ α, zeroPowerSum (Finset.univ.biUnion A) (fun q : XiZeroCopy => (q.1 : ℂ))
      (T ^ α * Real.exp (-ξ)) = ∑ i, ((E i α : ℝ) : ℂ) * B i α := by
    intro α
    unfold zeroPowerSum
    rw [Finset.sum_biUnion (by simpa using hdisj)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := zeroPowerSum_eq_bandSum (A i) hT0 (σ i) ξ α
    unfold zeroPowerSum at this
    simpa [hBdef, hEdef, hLdef] using this
  have hBcont : ∀ i, Continuous (B i) := by
    intro i
    simp only [hBdef]
    unfold GaloisForLFunctions.HTGeometry.mvBandSum
    fun_prop
  -- per-band integrals
  have hsepi : ∀ i, ∀ j ∈ A i, ∀ k ∈ A i, j ≠ k → D ≤ |bandFreq T j - bandFreq T k| := by
    intro i j hj k hk hjk
    exact hsep j (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hj⟩) k
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hk⟩) hjk
  have hlow := band_inner_ge_wide (A i₀) hT hD hℓ₀ hℓ₀ℓ ha hτ0 (hband i₀) (hsepi i₀) hc hξ
  have hup : ∀ i, (∫ α in a..a + ℓ, ‖B i α‖ ^ 2)
      ≤ mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * (A i).card) := by
    intro i
    exact band_inner_le_wide (A i) hT hD hℓ ha hτ0 (hband i) (hsepi i) hξ
  -- pointwise lower bound
  set m : ℝ := (Fintype.card κ : ℝ) with hm
  set s : κ → ℝ := fun i => bandScalarSq T a b (σ i₀) (σ i) with hs
  have hs0 : ∀ i, 0 ≤ s i := fun i => by
    simp only [hs, bandScalarSq]
    exact le_max_of_le_left (Real.rpow_nonneg hT0.le _)
  have hpt : ∀ α ∈ Icc a b,
      E i₀ a ^ 2 * (1 / 2 * ‖B i₀ α‖ ^ 2 - m * ∑ i ∈ Finset.univ.erase i₀, s i * ‖B i α‖ ^ 2)
        ≤ ‖∑ i, ((E i α : ℝ) : ℂ) * B i α‖ ^ 2 := by
    intro α hα
    set G : ℂ := ∑ i ∈ Finset.univ.erase i₀, ((E i α / E i₀ α : ℝ) : ℂ) * B i α with hG
    have hfactor : ∑ i, ((E i α : ℝ) : ℂ) * B i α = ((E i₀ α : ℝ) : ℂ) * (B i₀ α + G) := by
      rw [← Finset.add_sum_erase (Finset.univ : Finset κ) (fun i => ((E i α : ℝ) : ℂ) * B i α)
        (Finset.mem_univ i₀), hG, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hne : (E i₀ α : ℝ) ≠ 0 := (hE0 i₀ α).ne'
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ hne]
    have hGsq : ‖G‖ ^ 2 ≤ m * ∑ i ∈ Finset.univ.erase i₀, s i * ‖B i α‖ ^ 2 := by
      have h1 : ‖G‖ ≤ ∑ i ∈ Finset.univ.erase i₀, (E i α / E i₀ α) * ‖B i α‖ := by
        simp only [hG]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (div_pos (hE0 i α) (hE0 i₀ α))]
      have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase i₀)
        (f := fun i => (E i α / E i₀ α) * ‖B i α‖)
      have hcard : ((Finset.univ.erase i₀).card : ℝ) ≤ m := by
        rw [hm, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        exact_mod_cast Nat.sub_le _ _
      have hrel : ∀ i, (E i α / E i₀ α) ^ 2 ≤ s i := by
        intro i
        have : E i α / E i₀ α = Real.exp (α * (σ i - σ i₀) * L) := by
          simp only [hEdef]
          rw [← Real.exp_sub]
          congr 1
          ring
        rw [this, ← Real.exp_nat_mul]
        have hT1 : 1 ≤ T := hT.le
        have : Real.exp (((2 : ℕ) : ℝ) * (α * (σ i - σ i₀) * L)) = T ^ (2 * α * (σ i - σ i₀)) := by
          rw [Real.rpow_def_of_pos hT0, hLdef]
          congr 1
          push_cast
          ring
        rw [this]
        exact rpow_rel_le_bandScalarSq hT1 hα
      have hsum0 : 0 ≤ ∑ i ∈ Finset.univ.erase i₀, ((E i α / E i₀ α) * ‖B i α‖) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      calc ‖G‖ ^ 2 ≤ (∑ i ∈ Finset.univ.erase i₀, (E i α / E i₀ α) * ‖B i α‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ ((Finset.univ.erase i₀).card : ℝ) *
            ∑ i ∈ Finset.univ.erase i₀, ((E i α / E i₀ α) * ‖B i α‖) ^ 2 := h2
        _ ≤ m * ∑ i ∈ Finset.univ.erase i₀, ((E i α / E i₀ α) * ‖B i α‖) ^ 2 :=
            mul_le_mul_of_nonneg_right hcard hsum0
        _ ≤ m * ∑ i ∈ Finset.univ.erase i₀, s i * ‖B i α‖ ^ 2 := by
            gcongr with i _
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right (hrel i) (sq_nonneg _)
    have hBG : 1 / 2 * ‖B i₀ α‖ ^ 2 - ‖G‖ ^ 2 ≤ ‖B i₀ α + G‖ ^ 2 := by
      have h1 : ‖B i₀ α‖ ≤ ‖B i₀ α + G‖ + ‖G‖ := by
        calc ‖B i₀ α‖ = ‖(B i₀ α + G) - G‖ := by ring_nf
          _ ≤ ‖B i₀ α + G‖ + ‖G‖ := norm_sub_le _ _
      nlinarith [norm_nonneg (B i₀ α), norm_nonneg (B i₀ α + G), norm_nonneg G,
        sq_nonneg (‖B i₀ α + G‖ - ‖G‖)]
    rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hE0 i₀ α), mul_pow]
    have hEmono : E i₀ a ^ 2 ≤ E i₀ α ^ 2 := by
      have : E i₀ a ≤ E i₀ α := by
        simp only [hEdef]
        apply Real.exp_le_exp.mpr
        have hσ' : 0 ≤ σ i₀ - 1 / 2 := by linarith
        have := hα.1
        have : a * (σ i₀ - 1 / 2) * L ≤ α * (σ i₀ - 1 / 2) * L := by gcongr
        linarith
      exact pow_le_pow_left₀ (hE0 i₀ a).le this 2
    set Y := 1 / 2 * ‖B i₀ α‖ ^ 2 - m * ∑ i ∈ Finset.univ.erase i₀, s i * ‖B i α‖ ^ 2 with hY
    have hYX : Y ≤ ‖B i₀ α + G‖ ^ 2 := by
      rw [hY]; linarith [hGsq, hBG]
    rcases le_or_gt Y 0 with hY0 | hY0
    · calc E i₀ a ^ 2 * Y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hY0
        _ ≤ _ := by positivity
    · calc E i₀ a ^ 2 * Y ≤ E i₀ α ^ 2 * Y := mul_le_mul_of_nonneg_right hEmono hY0.le
        _ ≤ E i₀ α ^ 2 * ‖B i₀ α + G‖ ^ 2 := mul_le_mul_of_nonneg_left hYX (sq_nonneg _)
  -- integrate
  have hcontZ : Continuous (fun α => ‖∑ i, ((E i α : ℝ) : ℂ) * B i α‖ ^ 2) := by
    have : Continuous (fun α => ∑ i, ((E i α : ℝ) : ℂ) * B i α) := by
      refine continuous_finsetSum _ fun i _ => ?_
      refine (Complex.continuous_ofReal.comp ?_).mul (hBcont i)
      simp only [hEdef]
      fun_prop
    exact this.norm.pow 2
  have hcontW : Continuous (fun α =>
      E i₀ a ^ 2 * (1 / 2 * ‖B i₀ α‖ ^ 2 - m * ∑ i ∈ Finset.univ.erase i₀, s i * ‖B i α‖ ^ 2)) := by
    refine continuous_const.mul ((continuous_const.mul ((hBcont i₀).norm.pow 2)).sub
      (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul ((hBcont i).norm.pow 2))))
  have hint : (∫ α in a..b, E i₀ a ^ 2 *
      (1 / 2 * ‖B i₀ α‖ ^ 2 - m * ∑ i ∈ Finset.univ.erase i₀, s i * ‖B i α‖ ^ 2))
      ≤ ∫ α in a..b, ‖∑ i, ((E i α : ℝ) : ℂ) * B i α‖ ^ 2 :=
    intervalIntegral.integral_mono_on hab' (hcontW.intervalIntegrable _ _)
      (hcontZ.intervalIntegrable _ _) hpt
  have hlin : (∫ α in a..b, E i₀ a ^ 2 *
      (1 / 2 * ‖B i₀ α‖ ^ 2 - m * ∑ i ∈ Finset.univ.erase i₀, s i * ‖B i α‖ ^ 2))
      = E i₀ a ^ 2 * (1 / 2 * (∫ α in a..b, ‖B i₀ α‖ ^ 2)
          - m * ∑ i ∈ Finset.univ.erase i₀, s i * ∫ α in a..b, ‖B i α‖ ^ 2) := by
    have hsum : (∑ i ∈ Finset.univ.erase i₀, ∫ α in a..b, s i * ‖B i α‖ ^ 2)
        = ∑ i ∈ Finset.univ.erase i₀, s i * ∫ α in a..b, ‖B i α‖ ^ 2 :=
      Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
    have hf : IntervalIntegrable (fun α => 1 / 2 * ‖B i₀ α‖ ^ 2) volume a b :=
      (continuous_const.mul ((hBcont i₀).norm.pow 2)).intervalIntegrable _ _
    have hg : IntervalIntegrable (fun α => m * ∑ i ∈ Finset.univ.erase i₀, s i * ‖B i α‖ ^ 2)
        volume a b :=
      (continuous_const.mul (continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((hBcont i).norm.pow 2))).intervalIntegrable _ _
    have hfs : ∀ i ∈ Finset.univ.erase i₀,
        IntervalIntegrable (fun α => s i * ‖B i α‖ ^ 2) volume a b := fun i _ =>
      (continuous_const.mul ((hBcont i).norm.pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hf hg,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum hfs, hsum]
  rw [hlin] at hint
  -- assemble with the band bounds
  have hEa : E i₀ a ^ 2 = Real.exp (2 * (a * (σ i₀ - 1 / 2) * Real.log T)) := by
    simp only [hEdef, hLdef]
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hsumle : ∑ i ∈ Finset.univ.erase i₀, s i * ∫ α in a..b, ‖B i α‖ ^ 2
      ≤ ∑ i ∈ Finset.univ.erase i₀, s i *
          (mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * (A i).card)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hb]
    exact mul_le_mul_of_nonneg_left (hup i) (hs0 i)
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hbracket : 1 / 2 * (mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * (A i₀).card))
      - m * ∑ i ∈ Finset.univ.erase i₀, s i *
          (mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * (A i).card))
      ≤ 1 / 2 * (∫ α in a..b, ‖B i₀ α‖ ^ 2)
          - m * ∑ i ∈ Finset.univ.erase i₀, s i * ∫ α in a..b, ‖B i α‖ ^ 2 := by
    rw [hb]
    have := mul_le_mul_of_nonneg_left hsumle hm0
    rw [hb] at this
    linarith [hlow, this]
  have hE2 : 0 ≤ E i₀ a ^ 2 := sq_nonneg _
  calc Real.exp (2 * (a * (σ i₀ - 1 / 2) * Real.log T)) *
        (1 / 2 * (mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * (A i₀).card))
          - m * ∑ i ∈ Finset.univ.erase i₀, s i *
              (mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * (A i).card)))
      = E i₀ a ^ 2 * (1 / 2 * (mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * (A i₀).card))
          - m * ∑ i ∈ Finset.univ.erase i₀, s i *
              (mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * (A i).card))) := by
        rw [hEa]
    _ ≤ E i₀ a ^ 2 * (1 / 2 * (∫ α in a..b, ‖B i₀ α‖ ^ 2)
          - m * ∑ i ∈ Finset.univ.erase i₀, s i * ∫ α in a..b, ‖B i α‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbracket hE2
    _ ≤ ∫ α in a..b, ‖∑ i, ((E i α : ℝ) : ℂ) * B i α‖ ^ 2 := hint
    _ = _ := by
        rw [hb]
        refine intervalIntegral.integral_congr fun α _ => ?_
        rw [hdecomp α]

/-- **Several wide bands over a scale window.** -/
theorem multiBand_block_window_ge_wide {κ : Type} [Fintype κ] [DecidableEq κ] (A : κ → Finset XiZeroCopy)
    (hdisj : (Set.univ : Set κ).PairwiseDisjoint A) (σ : κ → ℝ) (i₀ : κ)
    {T D a ℓ ℓ₀ τ : ℝ} (hT : 1 < T) (hD : 0 < D) (hℓ₀ : 0 ≤ ℓ₀) (hℓ₀ℓ : ℓ₀ ≤ ℓ) (ha : 0 ≤ a)
    (hτ0 : 0 ≤ τ) (hσ : 1 / 2 ≤ σ i₀)
    (hband : ∀ i, ∀ j ∈ A i, σ i ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ i + τ / Real.log T)
    (hsep : ∀ j ∈ Finset.univ.biUnion A, ∀ k ∈ Finset.univ.biUnion A, j ≠ k →
      D ≤ |bandFreq T j - bandFreq T k|)
    (hc : 0 ≤ mvWideBandConstant ℓ₀ D τ) :
    2 * Real.exp (-2) * (Real.exp (2 * (a * (σ i₀ - 1 / 2) * Real.log T)) *
      (1 / 2 * (mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * (A i₀).card))
        - (Fintype.card κ : ℝ) * ∑ i ∈ Finset.univ.erase i₀,
            bandScalarSq T a (a + ℓ) (σ i₀) (σ i) *
              (mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * (A i).card))))
      ≤ ∫ α in a..a + ℓ, (montgomeryForm (Finset.univ.biUnion A)
          (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re :=
  montgomeryForm_window_ge_of_inner (Finset.univ.biUnion A) (by linarith) (le_trans hℓ₀ hℓ₀ℓ) _
    (fun ξ hξ => multiBand_inner_ge_wide A hdisj σ i₀ hT hD hℓ₀ hℓ₀ℓ ha hτ0 hσ hband hsep hc hξ)

/-- **Dominant-band isolation law, wide bands.** -/
theorem eventually_card_dominantBand_le_wide {a ℓ ℓ₀ δ₀ D τ : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hab : a + ℓ < 1) (hwin : 2 * (a + ℓ) ≤ 3 * a)
    (hδ₀ : 0 < δ₀) (hD : 0 < D) (hτ0 : 0 ≤ τ) (hℓ₀ : 0 ≤ ℓ₀) (hℓ₀ℓ : ℓ₀ ≤ ℓ)
    (hκ : 0 < mvWideBandConstant ℓ₀ D τ) :
    ∀ᶠ T : ℝ in atTop, ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : κ → Finset XiZeroCopy)
      (σ : κ → ℝ) (i₀ : κ), (Set.univ : Set κ).PairwiseDisjoint A →
      Finset.univ.biUnion A ⊆ zeroWindow T → 1 / 2 + 4 * δ₀ ≤ σ i₀ → (∀ i, 1 / 2 ≤ σ i) →
      (∀ i, ∀ j ∈ A i, σ i ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ i + τ / Real.log T) →
      (∀ k ∈ zeroWindow T \ Finset.univ.biUnion A, (k.1 : ℂ).re ≤ 1 / 2 + δ₀) →
      (∀ j ∈ Finset.univ.biUnion A, ∀ k ∈ Finset.univ.biUnion A, j ≠ k →
        D ≤ |bandFreq T j - bandFreq T k|) →
      ((Fintype.card κ : ℝ) * ∑ i ∈ Finset.univ.erase i₀,
          bandScalarSq T a (a + ℓ) (σ i₀) (σ i) *
            (mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * (A i).card))
        ≤ 1 / 4 * (mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * (A i₀).card))) →
      (∑ i, ((A i).card : ℝ) * T ^ ((a + ℓ) * (σ i - 1 / 2))
        ≤ 2 * (A i₀).card * T ^ ((a + ℓ) * (σ i₀ - 1 / 2))) →
      ((A i₀).card : ℝ) ≤ (4 * ℓ * Real.exp 3 / (Real.pi * mvWideBandConstant ℓ₀ D τ)) *
        T ^ (1 - 2 * a * (σ i₀ - 1 / 2)) * Real.log T := by
  classical
  set b := a + ℓ with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  have hb1 : b < 1 := hab
  have hab' : a ≤ b := by rw [hb]; linarith
  set C₀ := xiLineTwoLogDerivConstant with hC₀
  have hC₀0 : 0 ≤ C₀ := xiLineTwoLogDerivConstant_nonneg
  -- the exponent gap depends on `σ i₀`, which is quantified inside; we prove the eventual
  -- statement for each `σ`-value through a uniform gap in `δ₀`
  have hgapmin : ∀ δ : ℝ, 4 * δ₀ ≤ δ → b * δ / 12 ≤ 2 * a * δ - b * (δ₀ + δ) := by
    intro δ hδ
    have : 4 * b ≤ 6 * a := by rw [hb]; linarith
    nlinarith [hδ₀, hb0]
  set η₀ : ℝ := b * (4 * δ₀) / 12 with hη₀
  have hη₀pos : 0 < η₀ := by rw [hη₀]; positivity
  set ε₁ : ℝ := Real.exp (-3) * mvWideBandConstant ℓ₀ D τ / (1536 * Real.exp τ) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  -- eventual facts, uniform in the configuration
  have E1 := eventually_montgomeryForm_div_leadingOrder_uniform ha hab' hb1 (one_pos)
  have E2 := eventually_log_bounds
  have E3 := (tendsto_log_pow_div_rpow 1 hη₀pos).eventually (eventually_le_nhds hε₁pos)
  have E4 := Real.tendsto_log_atTop.eventually_ge_atTop C₀
  filter_upwards [E1, E2, E3, E4, eventually_gt_atTop (1 : ℝ)] with T e1 e2 e3 e4 hT1
  intro κ _ _ A σ i₀ hdisj hU hσ hσall hband hR hsep hdom hmass
  obtain ⟨hl1, _, _, hl4⟩ := e2
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  set L := Real.log T with hLdef
  obtain ⟨U, hUdef⟩ : ∃ U : Finset XiZeroCopy, U = Finset.univ.biUnion A := ⟨_, rfl⟩
  rw [← hUdef] at hU hR
  set δ := σ i₀ - 1 / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδ₀δ : 4 * δ₀ ≤ δ := by rw [hδ]; linarith
  set η := 2 * a * δ - b * (δ₀ + δ) with hη
  have hηη₀ : η₀ ≤ η := by
    rw [hη, hη₀]
    have := hgapmin δ hδ₀δ
    have h2 : b * (4 * δ₀) / 12 ≤ b * δ / 12 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hδ₀δ hb0.le
    linarith
  set N : ℝ := ((A i₀).card : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  -- (i) the band block over the window
  have hwindow := multiBand_block_window_ge_wide A hdisj σ i₀ hT1 hD hℓ₀ hℓ₀ℓ ha.le hτ0
    (by linarith) hband hsep hκ.le
  have hEexp : Real.exp (2 * (a * (σ i₀ - 1 / 2) * Real.log T)) = T ^ (2 * a * δ) := by
    rw [Real.rpow_def_of_pos hT0, hδ]
    congr 1
    ring
  rw [hEexp, ← hb, ← hUdef] at hwindow
  have hbracket : 1 / 4 * (mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * N))
      ≤ 1 / 2 * (mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * N))
        - (Fintype.card κ : ℝ) * ∑ i ∈ Finset.univ.erase i₀,
            bandScalarSq T a b (σ i₀) (σ i) *
              (mvWideBandUpperConstant a ℓ D τ * (Real.exp 1 * (A i).card)) := by
    linarith [hdom]
  have hlow : 1 / 2 * Real.exp (-3) * T ^ (2 * a * δ) * mvWideBandConstant ℓ₀ D τ * N
      ≤ ∫ α in a..b, (montgomeryForm U (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
    refine le_trans ?_ hwindow
    have hE0 : 0 ≤ T ^ (2 * a * δ) := Real.rpow_nonneg hT0.le _
    have h3 : Real.exp (-3) = Real.exp (-2) * Real.exp (-1) := by
      rw [← Real.exp_add]; norm_num
    rw [h3]
    have := mul_le_mul_of_nonneg_left hbracket (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.exp (-2)) hE0)
    calc 1 / 2 * (Real.exp (-2) * Real.exp (-1)) * T ^ (2 * a * δ) * mvWideBandConstant ℓ₀ D τ * N
        = 2 * Real.exp (-2) * T ^ (2 * a * δ) * (1 / 4 * (mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * N))) := by ring
      _ ≤ 2 * Real.exp (-2) * T ^ (2 * a * δ) * (1 / 2 *
          (mvWideBandConstant ℓ₀ D τ * (Real.exp (-1) * N))
          - (Fintype.card κ : ℝ) * ∑ i ∈ Finset.univ.erase i₀,
              bandScalarSq T a b (σ i₀) (σ i) *
                (mvWideBandUpperConstant a ℓ D τ *
                  (Real.exp 1 * (A i).card))) := this
      _ = _ := by ring
  -- (ii) pointwise upper bound for the union block at every scale of the window
  have hW : windowLog T ≤ 3 * L := by
    unfold windowLog
    linarith
  have hpt : ∀ α ∈ Icc a b,
      (montgomeryForm U (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ T / Real.pi * L + 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
    intro α hα
    have hα0 : 0 ≤ α := ha.le.trans hα.1
    have hx1 : 1 ≤ T ^ α := Real.one_le_rpow hT1.le hα0
    have hx0 : 0 < T ^ α := by linarith
    have hF : (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ T / Real.pi * L := by
      have h := e1 α hα
      have hNα : 0 < (T / (2 * Real.pi)) * (α * L) := by
        have : 0 < α := lt_of_lt_of_le ha hα.1
        positivity
      rw [abs_lt] at h
      have h2 := h.2
      rw [div_sub_one (ne_of_gt hNα), div_lt_iff₀ hNα] at h2
      have hαL : α * L ≤ L := by
        have : α ≤ 1 := by linarith only [hα.2, hab]
        exact mul_le_of_le_one_left hL.le this
      calc (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          ≤ 1 * (T / (2 * Real.pi) * (α * L)) + T / (2 * Real.pi) * (α * L) := by
            linarith only [h2]
        _ = T / Real.pi * (α * L) := by ring
        _ ≤ T / Real.pi * L := by gcongr
    have hRα : ∀ k ∈ zeroWindow T \ U, zeroAmp (T ^ α) k ≤ (T ^ α) ^ δ₀ := by
      intro k hk
      unfold zeroAmp
      apply Real.rpow_le_rpow_of_exponent_le hx1
      linarith only [hR k hk]
    have hsplit := montgomeryForm_block_split hx0 U hU (Θ := (T ^ α) ^ δ₀) (by positivity) hRα
    -- amplitudes on the union
    have hampi : ∀ i, ∑ j ∈ A i, zeroAmp (T ^ α) j
        ≤ ((A i).card : ℝ) * (T ^ (b * (σ i - 1 / 2)) * Real.exp τ) := by
      intro i
      have hone : ∀ j ∈ A i, zeroAmp (T ^ α) j ≤ T ^ (b * (σ i - 1 / 2)) * Real.exp τ := by
        intro j hj
        obtain ⟨_, hj2⟩ := hband i j hj
        unfold zeroAmp
        rw [← Real.rpow_mul hT0.le]
        have hexp : α * ((j.1 : ℂ).re - 1 / 2) ≤ b * (σ i - 1 / 2) + τ / L := by
          have h1 : (j.1 : ℂ).re - 1 / 2 ≤ (σ i - 1 / 2) + τ / L := by linarith
          have h2 : 0 ≤ (σ i - 1 / 2) + τ / L := by
            have := hσall i
            have : 0 ≤ τ / L := by positivity
            linarith only [this, hσall i]
          calc α * ((j.1 : ℂ).re - 1 / 2) ≤ α * ((σ i - 1 / 2) + τ / L) := by gcongr
            _ ≤ b * ((σ i - 1 / 2) + τ / L) := mul_le_mul_of_nonneg_right hα.2 h2
            _ = b * (σ i - 1 / 2) + b * (τ / L) := by ring
            _ ≤ b * (σ i - 1 / 2) + τ / L := by
                have : b * (τ / L) ≤ 1 * (τ / L) :=
                  mul_le_mul_of_nonneg_right hb1.le (by positivity)
                linarith
        calc T ^ (α * ((j.1 : ℂ).re - 1 / 2)) ≤ T ^ (b * (σ i - 1 / 2) + τ / L) :=
              Real.rpow_le_rpow_of_exponent_le hT1.le hexp
          _ = T ^ (b * (σ i - 1 / 2)) * T ^ (τ / L) := Real.rpow_add hT0 _ _
          _ = T ^ (b * (σ i - 1 / 2)) * Real.exp τ := by
              congr 1
              rw [Real.rpow_def_of_pos hT0, ← hLdef]
              congr 1
              field_simp
      calc ∑ j ∈ A i, zeroAmp (T ^ α) j ≤ ∑ _j ∈ A i, T ^ (b * (σ i - 1 / 2)) * Real.exp τ :=
            Finset.sum_le_sum hone
        _ = ((A i).card : ℝ) * (T ^ (b * (σ i - 1 / 2)) * Real.exp τ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hamp : ∑ j ∈ U, zeroAmp (T ^ α) j ≤ 2 * N * (T ^ (b * δ) * Real.exp τ) := by
      have hdisj' : (↑(Finset.univ : Finset κ) : Set κ).PairwiseDisjoint A := by
        simpa using hdisj
      rw [hUdef, Finset.sum_biUnion hdisj']
      calc ∑ i, ∑ j ∈ A i, zeroAmp (T ^ α) j
          ≤ ∑ i, ((A i).card : ℝ) * (T ^ (b * (σ i - 1 / 2)) * Real.exp τ) :=
            Finset.sum_le_sum fun i _ => hampi i
        _ = Real.exp τ * ∑ i, ((A i).card : ℝ) * T ^ (b * (σ i - 1 / 2)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ Real.exp τ * (2 * N * T ^ (b * (σ i₀ - 1 / 2))) := by
            rw [hb, hN]
            exact mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
        _ = 2 * N * (T ^ (b * δ) * Real.exp τ) := by rw [hδ]; ring
    have hΘ : (T ^ α) ^ δ₀ ≤ T ^ (b * δ₀) := by
      rw [← Real.rpow_mul hT0.le]
      apply Real.rpow_le_rpow_of_exponent_le hT1.le
      exact mul_le_mul_of_nonneg_right hα.2 hδ₀.le
    have hcross : 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ U, zeroAmp (T ^ α) j
        ≤ 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
      have hsum0 : 0 ≤ ∑ j ∈ U, zeroAmp (T ^ α) j :=
        Finset.sum_nonneg fun j _ => zeroAmp_nonneg hx0.le j
      have hW0 : 0 ≤ windowLog T := windowLog_nonneg hT0.le
      calc 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ U, zeroAmp (T ^ α) j
          ≤ 64 * T ^ (b * δ₀) * (3 * L) * (2 * N * (T ^ (b * δ) * Real.exp τ)) := by
            gcongr
        _ = 384 * Real.exp τ * L * N * (T ^ (b * δ₀) * T ^ (b * δ)) := by ring
        _ = 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
            rw [← Real.rpow_add hT0, show b * δ₀ + b * δ = b * (δ₀ + δ) by ring]
    have h1 := sub_le_iff_le_add.mp hsplit
    calc (montgomeryForm U (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          + 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ U, zeroAmp (T ^ α) j := h1
      _ ≤ T / Real.pi * L + 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := add_le_add hF hcross
  -- (iii) integrate the pointwise bound
  have hcontF := continuous_montgomeryForm_rpow U hT0
  have hup : (∫ α in a..b, (montgomeryForm U (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
      ≤ ℓ * (T / Real.pi * L + 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) := by
    have this : (∫ α in a..b, (montgomeryForm U (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
        ≤ ∫ _α in a..b, (T / Real.pi * L + 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) :=
      intervalIntegral.integral_mono_on hab' (hcontF.intervalIntegrable _ _)
        intervalIntegrable_const hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hba : b - a = ℓ := by rw [hb]; ring
    rw [hba] at this
    exact this
  -- (iv) the cross term is dominated by the detection term
  have hgap : 384 * Real.exp τ * L * T ^ (b * (δ₀ + δ))
      ≤ 1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ (2 * a * δ) := by
    have hpow : T ^ (2 * a * δ) = T ^ η * T ^ (b * (δ₀ + δ)) := by
      rw [← Real.rpow_add hT0, hη]; ring_nf
    rw [hpow]
    have hTη : 0 < T ^ η := Real.rpow_pos_of_pos hT0 η
    have hTη₀ : 0 < T ^ η₀ := Real.rpow_pos_of_pos hT0 η₀
    have hTb : 0 < T ^ (b * (δ₀ + δ)) := Real.rpow_pos_of_pos hT0 _
    have hlogT : L ≤ ε₁ * T ^ η₀ := by
      have h := e3
      simp only [pow_one] at h
      rwa [div_le_iff₀ hTη₀] at h
    have hηmono : T ^ η₀ ≤ T ^ η := Real.rpow_le_rpow_of_exponent_le hT1.le hηη₀
    have : 384 * Real.exp τ * L ≤ 1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ η := by
      calc 384 * Real.exp τ * L ≤ 384 * Real.exp τ * (ε₁ * T ^ η₀) := by gcongr
        _ = 1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ η₀ := by
            rw [hε₁]; field_simp; ring
        _ ≤ 1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ η := by gcongr
    calc 384 * Real.exp τ * L * T ^ (b * (δ₀ + δ))
        ≤ 1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ η * T ^ (b * (δ₀ + δ)) := by gcongr
      _ = _ := by ring
  -- conclude
  have hmain : 1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ (2 * a * δ) * N ≤ ℓ * (T / Real.pi * L) := by
    have h1 : 1 / 2 * Real.exp (-3) * T ^ (2 * a * δ) * mvWideBandConstant ℓ₀ D τ * N
        ≤ ℓ * (T / Real.pi * L) + ℓ * (384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) := by
      linarith only [hlow, hup]
    have h2 : ℓ * (384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)))
        ≤ 1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ (2 * a * δ) * N := by
      have hℓ1 : ℓ ≤ 1 := by linarith
      calc ℓ * (384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)))
          = ℓ * N * (384 * Real.exp τ * L * T ^ (b * (δ₀ + δ))) := by ring
        _ ≤ 1 * N * (1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ (2 * a * δ)) := by
            gcongr
        _ = _ := by ring
    linarith only [h1, h2]
  have hTpow : 0 < T ^ (2 * a * δ) := Real.rpow_pos_of_pos hT0 _
  have hfinal : N ≤ (4 * ℓ * Real.exp 3 / (Real.pi * mvWideBandConstant ℓ₀ D τ)) * (T / T ^ (2 * a * δ)) * L := by
    have hpos : 0 < 1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ (2 * a * δ) := by positivity
    rw [show 1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ (2 * a * δ) * N
        = N * (1 / 4 * Real.exp (-3) * mvWideBandConstant ℓ₀ D τ * T ^ (2 * a * δ)) by ring,
      ← le_div_iff₀ hpos] at hmain
    refine hmain.trans (le_of_eq ?_)
    rw [Real.exp_neg]
    field_simp
  have hdiv : T / T ^ (2 * a * δ) = T ^ (1 - 2 * a * δ) := by
    rw [Real.rpow_sub hT0, Real.rpow_one]
  rw [hdiv] at hfinal
  exact hfinal


end

end RHTower
