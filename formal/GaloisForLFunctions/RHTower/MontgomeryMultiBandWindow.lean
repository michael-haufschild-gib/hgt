import GaloisForLFunctions.RHTower.MontgomerySingleBandWindow

/-!
# Several bands over a scale window

For a disjoint family of bands `A_i` (real parts in `[σ_i, σ_i + τ/log T]`) whose union is
`D`-separated in mean-spacing units, the window integral of the pair form of the union is at
least `T^{2a(σ_{i₀}−1/2)}` times `½ c_low(i₀) e^{−1} N_{i₀}` minus the other bands' contributions
`m · s̄_i² · c_up(i) · e · N_i`, where `s̄_i² = max(T^{2a(σ_i−σ_{i₀})}, T^{2b(σ_i−σ_{i₀})})` is the
endpoint value of the relative amplitude.  Flattening at `i₀` makes its coefficients constant up to
the band width; every other band is a band sum times a monotone scalar.
-/

open Complex MeasureTheory Set Finset
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The Montgomery–Vaughan band upper constant. -/
def mvBandUpperConstant (ℓ D τ : ℝ) (K N : ℕ) : ℝ :=
  2 * (ℓ + 26 / (Real.pi * D))
    + 8 * (ℓ + 26 / (Real.pi * D)) * ∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ)
    + 4 * ℓ * (N : ℝ) * (τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K))) ^ 2

theorem mvBandUpperConstant_nonneg {ℓ D τ : ℝ} (hℓ : 0 ≤ ℓ) (hD : 0 < D) (hτ : 0 ≤ τ) (K N : ℕ) :
    0 ≤ mvBandUpperConstant ℓ D τ K N := by
  unfold mvBandUpperConstant
  have h1 : 0 ≤ ℓ + 26 / (Real.pi * D) := add_nonneg hℓ (by positivity)
  have h2 : 0 ≤ ∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ) :=
    Finset.sum_nonneg fun m _ => by positivity
  have h3 : 0 ≤ (τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K))) ^ 2 := sq_nonneg _
  have h4 : 0 ≤ 4 * ℓ * (N : ℝ) := by positivity
  nlinarith [mul_nonneg h1 h2, mul_nonneg h4 h3]

/-- Squared endpoint bound for the relative amplitude of band `σ` against band `σ₀`. -/
def bandScalarSq (T a b σ₀ σ : ℝ) : ℝ :=
  max (T ^ (2 * a * (σ - σ₀))) (T ^ (2 * b * (σ - σ₀)))

/-- The relative amplitude `T^{2α(σ−σ₀)}` is bounded by its endpoint values. -/
theorem rpow_rel_le_bandScalarSq {T a b σ₀ σ α : ℝ} (hT : 1 ≤ T) (hα : α ∈ Icc a b) :
    T ^ (2 * α * (σ - σ₀)) ≤ bandScalarSq T a b σ₀ σ := by
  unfold bandScalarSq
  rcases le_or_gt 0 (σ - σ₀) with h | h
  · refine le_max_of_le_right ?_
    apply Real.rpow_le_rpow_of_exponent_le hT
    have := hα.2
    nlinarith
  · refine le_max_of_le_left ?_
    apply Real.rpow_le_rpow_of_exponent_le hT
    have := hα.1
    nlinarith

/-- Lower bound for one band's inner scale integral (constant coefficients up to the band). -/
theorem band_inner_ge (A : Finset XiZeroCopy) {T σ D a ℓ τ : ℝ} (hT : 1 < T)
    (hD : 0 < D) (hℓ : 0 ≤ ℓ) (ha : 0 ≤ a) (hab : a + ℓ ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hband : ∀ j ∈ A, σ ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ + τ / Real.log T)
    (hsep : ∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|)
    {K : ℕ} (hK : 1 ≤ K) (hc : 0 ≤ mvBandConstant ℓ D τ K A.card) {ξ : ℝ} (hξ : ξ ∈ Icc (-1 : ℝ) 1) :
    mvBandConstant ℓ D τ K A.card * (Real.exp (-1) * A.card)
      ≤ ∫ α in a..a + ℓ, ‖GaloisForLFunctions.HTGeometry.mvBandSum (fun j : A => bandFreq T j)
          (fun j : A => bandCoeff ξ j) (fun j : A => bandTheta T σ j) α‖ ^ 2 := by
  classical
  have hL : 0 < Real.log T := Real.log_pos hT
  set u : A → ℝ := fun j => bandFreq T j with hu
  set d : A → ℂ := fun j => bandCoeff ξ j with hd
  set θ : A → ℝ := fun j => bandTheta T σ j with hθ
  have hθb : ∀ r : A, |θ r| ≤ τ := by
    intro r
    obtain ⟨h1, h2⟩ := hband r.1 r.2
    simp only [hθ, bandTheta]
    have h0 : 0 ≤ (((r.1).1 : ℂ).re - σ) * Real.log T := mul_nonneg (by linarith) hL.le
    rw [abs_of_nonneg h0]
    have h3 : ((r.1).1 : ℂ).re - σ ≤ τ / Real.log T := by linarith
    calc (((r.1).1 : ℂ).re - σ) * Real.log T ≤ (τ / Real.log T) * Real.log T := by gcongr
      _ = τ := by field_simp
  have hsep' : ∀ r s : A, r ≠ s → D ≤ |u r - u s| := by
    intro r s hrs
    exact hsep r.1 r.2 s.1 s.2 (fun h => hrs (Subtype.ext h))
  have h := GaloisForLFunctions.HTGeometry.interval_integral_normSq_mvBandSum_ge
    u d θ hD hℓ ha hab hτ0 hτ1 hθb hsep' hK
  have hcoef : Real.exp (-1) * A.card ≤ ∑ r : A, ‖d r‖ ^ 2 := by
    have hξ1 : |ξ| ≤ 1 := by rw [abs_le]; exact ⟨hξ.1, hξ.2⟩
    have : ∀ r : A, Real.exp (-1) ≤ ‖d r‖ ^ 2 := by
      intro r
      refine le_trans ?_ (normSq_bandCoeff_ge ξ r.1)
      apply Real.exp_le_exp.mpr
      linarith
    calc Real.exp (-1) * A.card = ∑ _r : A, Real.exp (-1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ r : A, ‖d r‖ ^ 2 := Finset.sum_le_sum fun r _ => this r
  have hcard : (Fintype.card A : ℝ) = A.card := by rw [Fintype.card_coe]
  rw [hcard] at h
  calc mvBandConstant ℓ D τ K A.card * (Real.exp (-1) * A.card)
      ≤ mvBandConstant ℓ D τ K A.card * ∑ r : A, ‖d r‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hcoef hc
    _ ≤ _ := by
        unfold mvBandConstant
        exact h

/-- Upper bound for one band's inner scale integral. -/
theorem band_inner_le (A : Finset XiZeroCopy) {T σ D a ℓ τ : ℝ} (hT : 1 < T)
    (hD : 0 < D) (hℓ : 0 ≤ ℓ) (ha : 0 ≤ a) (hab : a + ℓ ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hband : ∀ j ∈ A, σ ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ + τ / Real.log T)
    (hsep : ∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|)
    {K : ℕ} (hK : 1 ≤ K) {ξ : ℝ} (hξ : ξ ∈ Icc (-1 : ℝ) 1) :
    (∫ α in a..a + ℓ, ‖GaloisForLFunctions.HTGeometry.mvBandSum (fun j : A => bandFreq T j)
          (fun j : A => bandCoeff ξ j) (fun j : A => bandTheta T σ j) α‖ ^ 2)
      ≤ mvBandUpperConstant ℓ D τ K A.card * (Real.exp 1 * A.card) := by
  classical
  have hL : 0 < Real.log T := Real.log_pos hT
  set u : A → ℝ := fun j => bandFreq T j with hu
  set d : A → ℂ := fun j => bandCoeff ξ j with hd
  set θ : A → ℝ := fun j => bandTheta T σ j with hθ
  have hθb : ∀ r : A, |θ r| ≤ τ := by
    intro r
    obtain ⟨h1, h2⟩ := hband r.1 r.2
    simp only [hθ, bandTheta]
    have h0 : 0 ≤ (((r.1).1 : ℂ).re - σ) * Real.log T := mul_nonneg (by linarith) hL.le
    rw [abs_of_nonneg h0]
    have h3 : ((r.1).1 : ℂ).re - σ ≤ τ / Real.log T := by linarith
    calc (((r.1).1 : ℂ).re - σ) * Real.log T ≤ (τ / Real.log T) * Real.log T := by gcongr
      _ = τ := by field_simp
  have hsep' : ∀ r s : A, r ≠ s → D ≤ |u r - u s| := by
    intro r s hrs
    exact hsep r.1 r.2 s.1 s.2 (fun h => hrs (Subtype.ext h))
  have h := GaloisForLFunctions.HTGeometry.interval_integral_normSq_mvBandSum_le
    u d θ hD hℓ ha hab hτ0 hτ1 hθb hsep' hK
  have hcoef : ∑ r : A, ‖d r‖ ^ 2 ≤ Real.exp 1 * A.card := by
    have hξ1 : |ξ| ≤ 1 := by rw [abs_le]; exact ⟨hξ.1, hξ.2⟩
    have : ∀ r : A, ‖d r‖ ^ 2 ≤ Real.exp 1 := by
      intro r
      refine (normSq_bandCoeff_le ξ r.1).trans ?_
      exact Real.exp_le_exp.mpr hξ1
    calc ∑ r : A, ‖d r‖ ^ 2 ≤ ∑ _r : A, Real.exp 1 := Finset.sum_le_sum fun r _ => this r
      _ = Real.exp 1 * A.card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_comm]
  have hcard : (Fintype.card A : ℝ) = A.card := by rw [Fintype.card_coe]
  rw [hcard] at h
  have hup0 : 0 ≤ mvBandUpperConstant ℓ D τ K A.card :=
    mvBandUpperConstant_nonneg hℓ hD hτ0 K A.card
  calc _ ≤ mvBandUpperConstant ℓ D τ K A.card * ∑ r : A, ‖d r‖ ^ 2 := by
        unfold mvBandUpperConstant
        exact h
    _ ≤ _ := mul_le_mul_of_nonneg_left hcoef hup0

/-- **Several bands, inner scale integral, flattened at `i₀`.** -/
theorem multiBand_inner_ge {κ : Type} [Fintype κ] [DecidableEq κ] (A : κ → Finset XiZeroCopy)
    (hdisj : (Set.univ : Set κ).PairwiseDisjoint A) (σ : κ → ℝ) (i₀ : κ)
    {T D a ℓ τ : ℝ} (hT : 1 < T) (hD : 0 < D) (hℓ : 0 ≤ ℓ) (ha : 0 ≤ a) (hab : a + ℓ ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hσ : 1 / 2 ≤ σ i₀)
    (hband : ∀ i, ∀ j ∈ A i, σ i ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ i + τ / Real.log T)
    (hsep : ∀ j ∈ Finset.univ.biUnion A, ∀ k ∈ Finset.univ.biUnion A, j ≠ k →
      D ≤ |bandFreq T j - bandFreq T k|)
    {K : κ → ℕ} (hK : ∀ i, 1 ≤ K i) (hc : 0 ≤ mvBandConstant ℓ D τ (K i₀) (A i₀).card)
    {ξ : ℝ} (hξ : ξ ∈ Icc (-1 : ℝ) 1) :
    Real.exp (2 * (a * (σ i₀ - 1 / 2) * Real.log T)) *
      (1 / 2 * (mvBandConstant ℓ D τ (K i₀) (A i₀).card * (Real.exp (-1) * (A i₀).card))
        - (Fintype.card κ : ℝ) * ∑ i ∈ Finset.univ.erase i₀,
            bandScalarSq T a (a + ℓ) (σ i₀) (σ i) *
              (mvBandUpperConstant ℓ D τ (K i) (A i).card * (Real.exp 1 * (A i).card)))
      ≤ ∫ α in a..a + ℓ, ‖zeroPowerSum (Finset.univ.biUnion A) (fun q : XiZeroCopy => (q.1 : ℂ))
          (T ^ α * Real.exp (-ξ))‖ ^ 2 := by
  classical
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
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
  have hlow := band_inner_ge (A i₀) hT hD hℓ ha hab hτ0 hτ1 (hband i₀) (hsepi i₀) (hK i₀) hc hξ
  have hup : ∀ i, (∫ α in a..a + ℓ, ‖B i α‖ ^ 2)
      ≤ mvBandUpperConstant ℓ D τ (K i) (A i).card * (Real.exp 1 * (A i).card) := by
    intro i
    exact band_inner_le (A i) hT hD hℓ ha hab hτ0 hτ1 (hband i) (hsepi i) (hK i) hξ
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
          (mvBandUpperConstant ℓ D τ (K i) (A i).card * (Real.exp 1 * (A i).card)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hb]
    exact mul_le_mul_of_nonneg_left (hup i) (hs0 i)
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hbracket : 1 / 2 * (mvBandConstant ℓ D τ (K i₀) (A i₀).card * (Real.exp (-1) * (A i₀).card))
      - m * ∑ i ∈ Finset.univ.erase i₀, s i *
          (mvBandUpperConstant ℓ D τ (K i) (A i).card * (Real.exp 1 * (A i).card))
      ≤ 1 / 2 * (∫ α in a..b, ‖B i₀ α‖ ^ 2)
          - m * ∑ i ∈ Finset.univ.erase i₀, s i * ∫ α in a..b, ‖B i α‖ ^ 2 := by
    rw [hb]
    have := mul_le_mul_of_nonneg_left hsumle hm0
    rw [hb] at this
    linarith [hlow, this]
  have hE2 : 0 ≤ E i₀ a ^ 2 := sq_nonneg _
  calc Real.exp (2 * (a * (σ i₀ - 1 / 2) * Real.log T)) *
        (1 / 2 * (mvBandConstant ℓ D τ (K i₀) (A i₀).card * (Real.exp (-1) * (A i₀).card))
          - m * ∑ i ∈ Finset.univ.erase i₀, s i *
              (mvBandUpperConstant ℓ D τ (K i) (A i).card * (Real.exp 1 * (A i).card)))
      = E i₀ a ^ 2 * (1 / 2 * (mvBandConstant ℓ D τ (K i₀) (A i₀).card * (Real.exp (-1) * (A i₀).card))
          - m * ∑ i ∈ Finset.univ.erase i₀, s i *
              (mvBandUpperConstant ℓ D τ (K i) (A i).card * (Real.exp 1 * (A i).card))) := by
        rw [hEa]
    _ ≤ E i₀ a ^ 2 * (1 / 2 * (∫ α in a..b, ‖B i₀ α‖ ^ 2)
          - m * ∑ i ∈ Finset.univ.erase i₀, s i * ∫ α in a..b, ‖B i α‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbracket hE2
    _ ≤ ∫ α in a..b, ‖∑ i, ((E i α : ℝ) : ℂ) * B i α‖ ^ 2 := hint
    _ = _ := by
        rw [hb]
        refine intervalIntegral.integral_congr fun α _ => ?_
        rw [hdecomp α]

/-- **Several bands over a scale window.** -/
theorem multiBand_block_window_ge {κ : Type} [Fintype κ] [DecidableEq κ] (A : κ → Finset XiZeroCopy)
    (hdisj : (Set.univ : Set κ).PairwiseDisjoint A) (σ : κ → ℝ) (i₀ : κ)
    {T D a ℓ τ : ℝ} (hT : 1 < T) (hD : 0 < D) (hℓ : 0 ≤ ℓ) (ha : 0 ≤ a) (hab : a + ℓ ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hσ : 1 / 2 ≤ σ i₀)
    (hband : ∀ i, ∀ j ∈ A i, σ i ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ i + τ / Real.log T)
    (hsep : ∀ j ∈ Finset.univ.biUnion A, ∀ k ∈ Finset.univ.biUnion A, j ≠ k →
      D ≤ |bandFreq T j - bandFreq T k|)
    {K : κ → ℕ} (hK : ∀ i, 1 ≤ K i) (hc : 0 ≤ mvBandConstant ℓ D τ (K i₀) (A i₀).card) :
    2 * Real.exp (-2) * (Real.exp (2 * (a * (σ i₀ - 1 / 2) * Real.log T)) *
      (1 / 2 * (mvBandConstant ℓ D τ (K i₀) (A i₀).card * (Real.exp (-1) * (A i₀).card))
        - (Fintype.card κ : ℝ) * ∑ i ∈ Finset.univ.erase i₀,
            bandScalarSq T a (a + ℓ) (σ i₀) (σ i) *
              (mvBandUpperConstant ℓ D τ (K i) (A i).card * (Real.exp 1 * (A i).card))))
      ≤ ∫ α in a..a + ℓ, (montgomeryForm (Finset.univ.biUnion A)
          (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re :=
  montgomeryForm_window_ge_of_inner (Finset.univ.biUnion A) (by linarith) hℓ _
    (fun ξ hξ => multiBand_inner_ge A hdisj σ i₀ hT hD hℓ ha hab hτ0 hτ1 hσ hband hsep hK hc hξ)

end

end RHTower
