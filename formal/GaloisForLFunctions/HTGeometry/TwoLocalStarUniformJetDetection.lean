import GaloisForLFunctions.HTGeometry.TwoLocalStarSpectralJetFrame

/-!
# Uniform spectral-jet detection on explicit two-local star slices

Multiplication by an affine star gap acts on Walsh coefficients by weighted
nearest-neighbor shifts of the subset index. A finite maximum principle bounds
all inverse-gap powers and their deviation from the zero-coupling packet. This
avoids the exponential dimension loss of an entrywise perturbation estimate.

For `m` longitudinal couplings with `4*(m+1)*sum_j |c_j| ≤ 1`, one fixed
mixed derivative retains at least half the maximal original Walsh coefficient.
The detector is selected before the coupling. Parseval transfers the estimate
to the Euclidean norm of every balanced real spectral covector, with total
derivative order at most `n+1`. An explicit parametrization supplies the entire
family without an assumed source-suppression or nondegeneracy certificate.

These are literal derivatives of the characteristic roots of the two-local
star matrices already realized in the imported module. The transverse second
derivative is evaluated at zero. The longitudinal neighborhood is explicit,
but this is not a full-dimensional neighborhood in all local-Hamiltonian
parameters. Different covectors may select different star slices. No quenched
incidence-action estimate, fibre-sheet bound, circuit exclusion, complexity
growth law, or black-hole consequence is claimed here.
-/

open scoped BigOperators Topology
open Filter

namespace GaloisForLFunctions.HTGeometry
noncomputable section

noncomputable local instance uniformStarBoolCubeFintype
    {I : Type*} [Fintype I] : Fintype (I → Bool) := Fintype.ofFinite _

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Maximum unnormalized Walsh coefficient of a real spectral packet. -/
def starWalshMax (β : (I → Bool) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun S : Finset I => |realStarWalshPacket β S|

omit [DecidableEq I] in
private theorem packet_le_starWalshMax (β : (I → Bool) → ℝ) (S : Finset I) :
    |realStarWalshPacket β S| ≤ starWalshMax β :=
  Finset.le_sup' (fun S : Finset I => |realStarWalshPacket β S|) (Finset.mem_univ S)

omit [DecidableEq I] in
private theorem starWalshMax_nonneg (β : (I → Bool) → ℝ) : 0 ≤ starWalshMax β :=
  (abs_nonneg (realStarWalshPacket β ∅)).trans (packet_le_starWalshMax β ∅)

omit [DecidableEq I] in
private theorem starWalshMax_le {β : (I → Bool) → ℝ} {M : ℝ}
    (h : ∀ S, |realStarWalshPacket β S| ≤ M) : starWalshMax β ≤ M :=
  Finset.sup'_le Finset.univ_nonempty _ (fun S _ => h S)

omit [DecidableEq I] in
private theorem exists_starWalshMax (β : (I → Bool) → ℝ) :
    ∃ S : Finset I, |realStarWalshPacket β S| = starWalshMax β := by
  obtain ⟨S, _, hS⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun S : Finset I => |realStarWalshPacket β S|)
  exact ⟨S, hS.symm⟩

private def starWalshToggle (S : Finset I) (j : I) : Finset I :=
  if j ∈ S then S.erase j else insert j S

omit [Fintype I] in
private theorem sign_mul_starCharacter (z : I → Bool) (S : Finset I) (j : I) :
    (if z j then (-1 : ℝ) else 1) * (∏ i ∈ S, if z i then (-1 : ℝ) else 1) =
      ∏ i ∈ starWalshToggle S j, if z i then (-1 : ℝ) else 1 := by
  unfold starWalshToggle
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    have hp := Finset.mul_prod_erase S (fun i => if z i then (-1 : ℝ) else 1) hj
    rw [← hp]
    cases z j <;> simp
  · rw [if_neg hj, Finset.prod_insert hj]

omit [DecidableEq I] in
private theorem realStarWalshPacket_sub (β γ : (I → Bool) → ℝ) (S : Finset I) :
    realStarWalshPacket (fun z => β z - γ z) S =
      realStarWalshPacket β S - realStarWalshPacket γ S := by
  simp only [realStarWalshPacket, sub_mul, Finset.sum_sub_distrib]

/-- Multiplication by the affine physical gap becomes a weighted nearest-neighbor
operator on Walsh subsets. No dimension factor is introduced. -/
private theorem realStarWalshPacket_mul_gap (β : (I → Bool) → ℝ) (c : I → ℝ) (S : Finset I) :
    realStarWalshPacket (fun z => β z * twoLocalStarGap 1 c z) S =
      realStarWalshPacket β S + ∑ j, c j * realStarWalshPacket β (starWalshToggle S j) := by
  simp only [realStarWalshPacket, twoLocalStarGap, mul_add, mul_one, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro z _
  rw [← sign_mul_starCharacter]
  ring

/-- Relative total coupling, not Hilbert-space dimension, controls the Walsh perturbation. -/
theorem realStarWalshPacket_gap_error (β : (I → Bool) → ℝ) (c : I → ℝ) (S : Finset I) :
    |realStarWalshPacket (fun z => β z * twoLocalStarGap 1 c z) S -
      realStarWalshPacket β S| ≤ (∑ j, |c j|) * starWalshMax β := by
  rw [realStarWalshPacket_mul_gap, add_sub_cancel_left]
  calc
    |∑ j, c j * realStarWalshPacket β (starWalshToggle S j)| ≤
        ∑ j, |c j * realStarWalshPacket β (starWalshToggle S j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |c j| * starWalshMax β := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (packet_le_starWalshMax β _) (abs_nonneg _)
    _ = (∑ j, |c j|) * starWalshMax β := (Finset.sum_mul _ _ _).symm

/-- Spectral packet after repeated division by the normalized affine star gap. -/
def starResolventPacket (β : (I → Bool) → ℝ) (c : I → ℝ) (r : ℕ) (z : I → Bool) : ℝ :=
  β z * (twoLocalStarGap 1 c z)⁻¹ ^ r

omit [DecidableEq I] in
@[simp] theorem starResolventPacket_zero (β : (I → Bool) → ℝ) (c : I → ℝ) :
    starResolventPacket β c 0 = β := by
  funext z
  simp [starResolventPacket]

omit [DecidableEq I] in
private theorem starResolventPacket_succ_mul_gap (β : (I → Bool) → ℝ) (c : I → ℝ)
    (hc : ∀ z, twoLocalStarGap 1 c z ≠ 0) (r : ℕ) :
    (fun z => starResolventPacket β c (r + 1) z * twoLocalStarGap 1 c z) =
      starResolventPacket β c r := by
  funext z
  simp only [starResolventPacket, pow_succ, mul_assoc, inv_mul_cancel₀ (hc z), mul_one]

private theorem starResolventPacket_step_error (β : (I → Bool) → ℝ) (c : I → ℝ)
    (hc : ∀ z, twoLocalStarGap 1 c z ≠ 0) (r : ℕ) (S : Finset I) :
    |realStarWalshPacket (starResolventPacket β c (r + 1)) S -
        realStarWalshPacket (starResolventPacket β c r) S| ≤
      (∑ j, |c j|) * starWalshMax (starResolventPacket β c (r + 1)) := by
  have h := realStarWalshPacket_gap_error (starResolventPacket β c (r + 1)) c S
  rw [starResolventPacket_succ_mul_gap β c hc r, abs_sub_comm] at h
  exact h

private theorem starResolventPacket_step_max (β : (I → Bool) → ℝ) (c : I → ℝ)
    (hc : ∀ z, twoLocalStarGap 1 c z ≠ 0) (r : ℕ) :
    (1 - ∑ j, |c j|) * starWalshMax (starResolventPacket β c (r + 1)) ≤
      starWalshMax (starResolventPacket β c r) := by
  obtain ⟨S, hS⟩ := exists_starWalshMax (starResolventPacket β c (r + 1))
  have herr := starResolventPacket_step_error β c hc r S
  have hprev := packet_le_starWalshMax (starResolventPacket β c r) S
  have htri := abs_add_le
    (realStarWalshPacket (starResolventPacket β c (r + 1)) S -
      realStarWalshPacket (starResolventPacket β c r) S)
    (realStarWalshPacket (starResolventPacket β c r) S)
  rw [sub_add_cancel, hS] at htri
  linarith

/-- A finite maximum-principle estimate for every resolvent power. -/
theorem starResolventPacket_max_bound (β : (I → Bool) → ℝ) (c : I → ℝ)
    (hc : ∀ z, twoLocalStarGap 1 c z ≠ 0) (hsmall : ∑ j, |c j| ≤ 1) (r : ℕ) :
    (1 - ∑ j, |c j|) ^ r * starWalshMax (starResolventPacket β c r) ≤ starWalshMax β := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : 0 ≤ (1 - ∑ j, |c j|) ^ r := pow_nonneg (sub_nonneg.mpr hsmall) _
    have h := mul_le_mul_of_nonneg_left (starResolventPacket_step_max β c hc r) hp
    rw [← mul_assoc, ← pow_succ] at h
    exact h.trans ih

/-- Perturbation from the zero-coupling Walsh packet, with no exponential dimension factor. -/
theorem starResolventPacket_deviation_bound (β : (I → Bool) → ℝ) (c : I → ℝ)
    (hc : ∀ z, twoLocalStarGap 1 c z ≠ 0) (hsmall : ∑ j, |c j| ≤ 1) (r : ℕ) :
    (1 - ∑ j, |c j|) ^ r *
      starWalshMax (fun z => starResolventPacket β c r z - β z) ≤
        (1 - (1 - ∑ j, |c j|) ^ r) * starWalshMax β := by
  induction r with
  | zero => simp [starWalshMax, realStarWalshPacket]
  | succ r ih =>
    let p : ℝ := 1 - ∑ j, |c j|
    have hp : 0 ≤ p := sub_nonneg.mpr hsmall
    have hrho : 0 ≤ ∑ j, |c j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have hstep : starWalshMax (fun z => starResolventPacket β c (r + 1) z - β z) ≤
        (∑ j, |c j|) * starWalshMax (starResolventPacket β c (r + 1)) +
          starWalshMax (fun z => starResolventPacket β c r z - β z) := by
      apply starWalshMax_le
      intro S
      rw [realStarWalshPacket_sub]
      have htri := abs_add_le
        (realStarWalshPacket (starResolventPacket β c (r + 1)) S -
          realStarWalshPacket (starResolventPacket β c r) S)
        (realStarWalshPacket (starResolventPacket β c r) S - realStarWalshPacket β S)
      have he := packet_le_starWalshMax
        (fun z => starResolventPacket β c r z - β z) S
      rw [realStarWalshPacket_sub] at he
      have hs := starResolventPacket_step_error β c hc r S
      rw [sub_add_sub_cancel] at htri
      linarith
    have h1 := mul_le_mul_of_nonneg_left hstep (pow_nonneg hp (r + 1))
    have h2 := mul_le_mul_of_nonneg_left
      (starResolventPacket_max_bound β c hc hsmall (r + 1)) hrho
    have h3 := mul_le_mul_of_nonneg_left ih hp
    change p ^ (r + 1) * _ ≤ (1 - p ^ (r + 1)) * _
    change p ^ r * _ ≤ (1 - p ^ r) * _ at ih
    change (∑ j, |c j|) * (p ^ (r + 1) * _) ≤ _ at h2
    change p * (p ^ r * _) ≤ p * ((1 - p ^ r) * _) at h3
    have hpdef : p + ∑ j, |c j| = 1 := by dsimp [p]; ring
    rw [pow_succ] at h1 h2 ⊢
    nlinarith

omit [DecidableEq I] in
private theorem normalizedStarGap_pos (c : I → ℝ) (hsmall : ∑ j, |c j| < 1)
    (z : I → Bool) : 0 < twoLocalStarGap 1 c z := by
  have hb : |∑ j, c j * (if z j then (-1 : ℝ) else 1)| ≤ ∑ j, |c j| := by
    calc
      _ ≤ ∑ j, |c j * (if z j then (-1 : ℝ) else 1)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        cases z j <;> simp
  have hl := neg_abs_le (∑ j, c j * (if z j then (-1 : ℝ) else 1))
  unfold twoLocalStarGap
  linarith

omit [DecidableEq I] in
private theorem small_starCoupling_lt_one (c : I → ℝ)
    (hsmall : 4 * ((Fintype.card I : ℝ) + 1) * (∑ j, |c j|) ≤ 1) :
    ∑ j, |c j| < 1 := by
  have hρ : 0 ≤ ∑ j, |c j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hm : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hm hρ]

/-- Uniform stability at every derivative order up to one plus the number of couplings.
The neighborhood shrinks only linearly in that number. -/
theorem starResolventPacket_uniform_error (β : (I → Bool) → ℝ) (c : I → ℝ)
    (hsmall : 4 * ((Fintype.card I : ℝ) + 1) * (∑ j, |c j|) ≤ 1)
    (r : ℕ) (hr : r ≤ Fintype.card I + 1) (S : Finset I) :
    |realStarWalshPacket (starResolventPacket β c r) S - realStarWalshPacket β S| ≤
      starWalshMax β / 2 := by
  let ρ : ℝ := ∑ j, |c j|
  have hρ : 0 ≤ ρ := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hρlt : ρ < 1 := small_starCoupling_lt_one c hsmall
  have hc : ∀ z, twoLocalStarGap 1 c z ≠ 0 :=
    fun z => ne_of_gt (normalizedStarGap_pos c hρlt z)
  have hrR : (r : ℝ) ≤ (Fintype.card I : ℝ) + 1 := by exact_mod_cast hr
  have hrρ : (r : ℝ) * ρ ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_right hrR hρ
    change 4 * ((Fintype.card I : ℝ) + 1) * ρ ≤ 1 at hsmall
    linarith
  have hber : 1 - (r : ℝ) * ρ ≤ (1 - ρ) ^ r := by
    simpa only [mul_neg, sub_eq_add_neg] using
      (one_add_mul_le_pow (a := -ρ) (by linarith) r)
  have hpow : 3 / 4 ≤ (1 - ρ) ^ r := by linarith
  have he := starResolventPacket_deviation_bound β c hc hρlt.le r
  change (1 - ρ) ^ r * _ ≤ (1 - (1 - ρ) ^ r) * _ at he
  have hE := starWalshMax_nonneg (fun z => starResolventPacket β c r z - β z)
  have hM := starWalshMax_nonneg β
  have hmax : starWalshMax (fun z => starResolventPacket β c r z - β z) ≤
      starWalshMax β / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hE,
      mul_nonneg (sub_nonneg.mpr hpow) hM]
  have h := packet_le_starWalshMax (fun z => starResolventPacket β c r z - β z) S
  rw [realStarWalshPacket_sub] at h
  exact h.trans hmax

omit [DecidableEq I] in
private theorem sqrt_energy_le_starWalshMax (β : (I → Bool) → ℝ) :
    Real.sqrt (∑ z, β z ^ (2 : ℕ)) ≤ starWalshMax β := by
  have hM := starWalshMax_nonneg β
  have hsum : (∑ S : Finset I, realStarWalshPacket β S ^ (2 : ℕ)) ≤
      ∑ _S : Finset I, starWalshMax β ^ (2 : ℕ) := by
    apply Finset.sum_le_sum
    intro S _
    have h := packet_le_starWalshMax β S
    have hsq := sq_abs (realStarWalshPacket β S)
    nlinarith [abs_nonneg (realStarWalshPacket β S)]
  rw [sum_sq_realStarWalshPacket] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_finset,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hsum
  have hD : (0 : ℝ) < 2 ^ Fintype.card I := pow_pos (by norm_num) _
  exact Real.sqrt_le_iff.mpr ⟨hM, by nlinarith⟩

/-- One fixed mixed derivative detects a real packet throughout the explicit coupling ball.
The detector is chosen before the coupling. The bound is independent of replica count. -/
theorem exists_uniform_twoLocalStarCurvature_detection (β : (I → Bool) → ℝ) :
    ∃ S : Finset I, S.card + 2 ≤ Fintype.card I + 2 ∧
      ∀ c : I → ℝ, 4 * ((Fintype.card I : ℝ) + 1) * (∑ j, |c j|) ≤ 1 →
        starWalshMax β / 2 ≤
          |orderedStarCouplingDeriv S.toList (twoLocalStarCurvature 1 β) c| := by
  obtain ⟨S, hS⟩ := exists_starWalshMax β
  refine ⟨S, Nat.add_le_add_right (Finset.card_le_univ S) 2, ?_⟩
  intro c hsmall
  have herr := starResolventPacket_uniform_error β c hsmall (S.card + 1)
    (Nat.add_le_add_right (Finset.card_le_univ S) 1) S
  have htri := abs_sub_le (realStarWalshPacket β S)
    (realStarWalshPacket (starResolventPacket β c (S.card + 1)) S) 0
  rw [sub_zero, sub_zero, abs_sub_comm, hS] at htri
  have hpacket : starWalshMax β / 2 ≤
      |realStarWalshPacket (starResolventPacket β c (S.card + 1)) S| := by linarith
  have hc : ∀ z, twoLocalStarGap 1 c z ≠ 0 :=
    fun z => ne_of_gt (normalizedStarGap_pos c (small_starCoupling_lt_one c hsmall) z)
  have hform := orderedStarCouplingDeriv_curvature 1 β S.toList c hc
  simp only [Finset.length_toList, Finset.prod_map_toList] at hform
  have hsum : (∑ z, β z * (∏ j ∈ S, if z j then (-1 : ℝ) else 1) *
      (twoLocalStarGap 1 c z)⁻¹ ^ (S.card + 1)) =
        realStarWalshPacket (starResolventPacket β c (S.card + 1)) S := by
    apply Finset.sum_congr rfl
    intro z _
    dsimp [realStarWalshPacket, starResolventPacket]
    ring
  rw [hsum] at hform
  rw [hform, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hfN : 1 ≤ S.card.factorial := Nat.factorial_pos _
  have hf : (1 : ℝ) ≤ (S.card.factorial : ℝ) := by exact_mod_cast hfN
  have habs := abs_nonneg (realStarWalshPacket (starResolventPacket β c (S.card + 1)) S)
  nlinarith

/-- Explicit parametrization of a dimension-controlled coupling neighborhood. -/
def normalizedStarCoupling (w : I → ℝ) (j : I) : ℝ :=
  w j / (4 * ((Fintype.card I : ℝ) + 1) * (1 + ∑ i, |w i|))

omit [DecidableEq I] in
theorem normalizedStarCoupling_small (w : I → ℝ) :
    4 * ((Fintype.card I : ℝ) + 1) * (∑ j, |normalizedStarCoupling w j|) ≤ 1 := by
  have hR : 0 ≤ ∑ j, |w j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hA : 0 < 4 * ((Fintype.card I : ℝ) + 1) := by positivity
  have hden : 0 < 4 * ((Fintype.card I : ℝ) + 1) * (1 + ∑ j, |w j|) :=
    mul_pos hA (by linarith)
  simp only [normalizedStarCoupling, abs_div, abs_of_pos hden, ← Finset.sum_div]
  calc
    _ = (∑ j, |w j|) / (1 + ∑ j, |w j|) := by field_simp
    _ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)

omit [DecidableEq I] in
private theorem actualStarCurvature_germ (β : (I → Bool) → ℝ) (constant : ℝ)
    (a : ℝ) (c : I → ℝ) (hc : ∀ z, 0 < twoLocalStarGap a c z) :
    (fun c' => deriv (deriv (blockSplitRelation constant β (twoLocalStarGap a c'))) 0)
      =ᶠ[𝓝 c] twoLocalStarCurvature a β := by
  have hpos : ∀ᶠ c' in 𝓝 c, ∀ z, 0 < twoLocalStarGap a c' z := by
    apply Filter.eventually_all.mpr
    intro z
    have hcont : Continuous (fun c' : I → ℝ => twoLocalStarGap a c' z) := by
      unfold twoLocalStarGap
      fun_prop
    exact hcont.continuousAt.eventually (Ioi_mem_nhds (hc z))
  filter_upwards [hpos] with c' hc'
  rw [(hasDerivAt_deriv_blockSplitRelation_zero constant β (twoLocalStarGap a c')
    (fun z => ne_of_gt (hc' z))).deriv]
  simp only [twoLocalStarCurvature]
  apply Finset.sum_congr rfl
  intro z _
  rw [abs_of_pos (hc' z), one_div]

/-- Unconditional, all-real-packet finite-type certificate on an explicit nonzero-sized
coupling neighborhood. The derivatives are literal derivatives of characteristic roots of
ordinary two-local star matrices, not an assigned jet or a presumed source estimate. -/
theorem exists_normalizedStar_actualSpectralJet_detection
    (β : (I → Bool) → ℝ) (constant : ℝ) :
    ∃ S : Finset I, S.card + 2 ≤ Fintype.card I + 2 ∧
      ∀ w : I → ℝ, Real.sqrt (∑ z, β z ^ (2 : ℕ)) / 2 ≤
        |orderedStarCouplingDeriv S.toList
          (fun c => deriv (deriv (blockSplitRelation constant β (twoLocalStarGap 1 c))) 0)
          (normalizedStarCoupling w)| := by
  obtain ⟨S, horder, hbound⟩ := exists_uniform_twoLocalStarCurvature_detection β
  refine ⟨S, horder, ?_⟩
  intro w
  have hs := normalizedStarCoupling_small w
  rw [orderedStarCouplingDeriv_congr S.toList
    (actualStarCurvature_germ β constant 1 (normalizedStarCoupling w)
      (fun z => normalizedStarGap_pos _ (small_starCoupling_lt_one _ hs) z))]
  have hb := hbound (normalizedStarCoupling w) hs
  have he := sqrt_energy_le_starWalshMax β
  linarith

omit [DecidableEq I] in
private theorem twoLocalStarGap_scale (a : ℝ) (c : I → ℝ) (z : I → Bool) :
    twoLocalStarGap a (fun j => a * c j) z = a * twoLocalStarGap 1 c z := by
  simp only [twoLocalStarGap, mul_add, mul_one, Finset.mul_sum, mul_assoc]

private theorem starCurvature_deriv_scale (a : ℝ) (ha : a ≠ 0)
    (β : (I → Bool) → ℝ) (S : Finset I) (c : I → ℝ)
    (hc : ∀ z, twoLocalStarGap 1 c z ≠ 0) :
    orderedStarCouplingDeriv S.toList (twoLocalStarCurvature a β) (fun j => a * c j) =
      (a⁻¹) ^ (S.card + 1) *
        orderedStarCouplingDeriv S.toList (twoLocalStarCurvature 1 β) c := by
  have hca : ∀ z, twoLocalStarGap a (fun j => a * c j) z ≠ 0 := by
    intro z
    rw [twoLocalStarGap_scale]
    exact mul_ne_zero ha (hc z)
  rw [orderedStarCouplingDeriv_curvature a β S.toList _ hca,
    orderedStarCouplingDeriv_curvature 1 β S.toList c hc]
  simp only [Finset.length_toList, twoLocalStarGap_scale, mul_inv_rev, mul_pow,
    ← mul_assoc, ← Finset.sum_mul]
  ring

/-- Scale-covariant uniform spectral detection. A single derivative works over the entire
relative coupling ball. Multiplying it by `a^(order-1)` removes the energy-scale choice. -/
theorem exists_scaledStar_actualSpectralJet_detection
    (a : ℝ) (ha : 0 < a) (β : (I → Bool) → ℝ) (constant : ℝ) :
    ∃ S : Finset I, S.card + 2 ≤ Fintype.card I + 2 ∧
      ∀ w : I → ℝ, starWalshMax β / 2 ≤
        a ^ (S.card + 1) * |orderedStarCouplingDeriv S.toList
          (fun c => deriv (deriv (blockSplitRelation constant β (twoLocalStarGap a c))) 0)
          (fun j => a * normalizedStarCoupling w j)| := by
  obtain ⟨S, horder, hbound⟩ := exists_uniform_twoLocalStarCurvature_detection β
  refine ⟨S, horder, ?_⟩
  intro w
  have hs := normalizedStarCoupling_small w
  have hp : ∀ z, 0 < twoLocalStarGap 1 (normalizedStarCoupling w) z :=
    fun z => normalizedStarGap_pos _ (small_starCoupling_lt_one _ hs) z
  have hpa : ∀ z, 0 < twoLocalStarGap a (fun j => a * normalizedStarCoupling w j) z := by
    intro z
    rw [twoLocalStarGap_scale]
    exact mul_pos ha (hp z)
  rw [orderedStarCouplingDeriv_congr S.toList
    (actualStarCurvature_germ β constant a _ hpa),
    starCurvature_deriv_scale a (ne_of_gt ha) β S _ (fun z => ne_of_gt (hp z)),
    abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr ha.le) _),
    ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt ha), one_pow, one_mul]
  exact hbound (normalizedStarCoupling w) hs

/-- Uniform detection on each star slice through the bounded common reference field.
All couplings and all real packets are admitted through an explicit parametrization;
no source suppression or nondegeneracy premise is assumed. -/
theorem commonReferenceStar_uniform_actualSpectralJet_detection
    (n : ℕ) (i : Fin n) (β : qubitEnvironment n i → ℝ) (constant : ℝ) :
    ∃ S : Finset {j : Fin n // j ≠ i}, S.card + 2 ≤ n + 1 ∧
      ∀ w : {j : Fin n // j ≠ i} → ℝ,
        starWalshMax β / 2 ≤
          |orderedStarCouplingDeriv S.toList
            (fun c => deriv (deriv (blockSplitRelation constant β
              (twoLocalStarGap (starJetReferenceField n i) c))) 0)
            (fun j => starJetReferenceField n i * normalizedStarCoupling w j)| := by
  have ha := starJetReferenceField_pos_le_one n i
  obtain ⟨S, horder, hbound⟩ := exists_scaledStar_actualSpectralJet_detection
    (starJetReferenceField n i) ha.1 β constant
  have hdim : Fintype.card {j : Fin n // j ≠ i} < n := by
    simpa using Fintype.card_subtype_lt (x := i) (p := fun j : Fin n => j ≠ i)
      (by simp)
  refine ⟨S, by omega, ?_⟩
  intro w
  have hp := pow_le_one₀ ha.1.le ha.2 (n := S.card + 1)
  have h := hbound w
  have hmul := mul_le_mul_of_nonneg_right hp (abs_nonneg
    (orderedStarCouplingDeriv S.toList
      (fun c => deriv (deriv (blockSplitRelation constant β
        (twoLocalStarGap (starJetReferenceField n i) c))) 0)
      (fun j => starJetReferenceField n i * normalizedStarCoupling w j)))
  exact h.trans (by simpa only [one_mul] using hmul)

/-- Every balanced nonzero real spectral covector admits one fixed spin and one fixed
mixed derivative, of total order at most `n+1`, which retain half of its Euclidean norm
throughout an explicit relative coupling ball. The transverse derivative is evaluated
at zero; this is not a full-ensemble small-tube estimate. -/
theorem balanced_real_character_uniform_starJet_detection
    (n : ℕ) (k : (Fin n → Bool) → ℝ)
    (hbalance : ∑ x, k x = 0) (hk : k ≠ 0) :
    ∃ (i : Fin n) (S : Finset {j : Fin n // j ≠ i}),
      S.card + 2 ≤ n + 1 ∧ ∀ w : {j : Fin n // j ≠ i} → ℝ,
        Real.sqrt (∑ x, k x ^ (2 : ℕ)) / 2 ≤
          |orderedStarCouplingDeriv S.toList
            (fun c => deriv (deriv (commonReferenceRealStarAction k i c)) 0)
            (fun j => starJetReferenceField n i * normalizedStarCoupling w j)| := by
  obtain ⟨B, hBmax⟩ := exists_starWalshMax k
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hk
  have hE : 0 < ∑ y, k y ^ (2 : ℕ) :=
    Finset.sum_pos' (fun y _ => sq_nonneg (k y))
      ⟨x, Finset.mem_univ x, sq_pos_of_ne_zero hx⟩
  have hM : 0 < starWalshMax k :=
    (Real.sqrt_pos.mpr hE).trans_le (sqrt_energy_le_starWalshMax k)
  have hB : B.Nonempty := by
    rcases B.eq_empty_or_nonempty with rfl | h
    · simp only [realStarWalshPacket, Finset.prod_empty, mul_one, hbalance, abs_zero] at hBmax
      linarith
    · exact h
  let i := B.min' hB
  let β : qubitEnvironment n i → ℝ :=
    fun z => k (edgeState i z false) - k (edgeState i z true)
  let m : qubitEnvironment n i → ℝ := fun z =>
    ∑ j : {j : Fin n // j ≠ i}, starJetReferenceField n j * (if z j then -1 else 1)
  let C : ℝ := ∑ z, (k (edgeEquiv i (0, z)) + k (edgeEquiv i (1, z))) * m z
  have hlarge : starWalshMax k ≤ starWalshMax β := by
    rw [← hBmax, realStarWalshPacket_edge k B i (B.min'_mem hB)]
    exact packet_le_starWalshMax β (B.subtype fun j => j ≠ i)
  have haction (c : {j : Fin n // j ≠ i} → ℝ) :
      commonReferenceRealStarAction k i c =
        blockSplitRelation C β (twoLocalStarGap (starJetReferenceField n i) c) := by
    funext u
    unfold commonReferenceRealStarAction
    rw [sum_blockSplitRoot_eq]
    rfl
  obtain ⟨S, horder, hbound⟩ :=
    commonReferenceStar_uniform_actualSpectralJet_detection n i β C
  refine ⟨i, S, horder, ?_⟩
  intro w
  simp_rw [haction]
  have h := hbound w
  have hroot := sqrt_energy_le_starWalshMax k
  linarith

end
end GaloisForLFunctions.HTGeometry
