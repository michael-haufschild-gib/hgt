import GaloisForLFunctions.ArithmeticScatteringHolography.TheExactRingdown

/-!
# The flux law, the edge theorem and energy balance

Green's identity is the flux law of the black hole: on the part of the graph below depth `K`, the failure
of `A` to be symmetric is the boundary flux through the cusps. Three consequences.

* **Causality from flux.** A resonance with nonreal `Y` has `|X|² < q`: it is damped
  (`normSq_lt_of_outgoing`). With `a = X²`, the same statement is `|a| < q`, the edge theorem. The argument
  uses only the positivity of the mass, so it holds on every black hole.
* **The mass law.** The mass of a resonant state below depth `K` is the flux at `K` divided by
  `1 - q/|Y|²` (`mass_law`): a Szegő kernel. Its core mass is the amplitude divided by the distance to the
  unitary circle (`core_mass_law`).
* **Energy balance.** Any two waves have a bilinear energy that changes only by flux
  (`energy_balance`). For a wave and its image under a symmetry the energy is a conserved charge.
-/

open Finset ComplexConjugate
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]

/-- The wave operator is real. -/
theorem waveOp_conj (q : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) :
    waveOp q (fun w => conj (f w)) v = conj (waveOp q f v) := by
  have hw (P : G) : conj (branchWeight P) = branchWeight P := by
    unfold branchWeight
    split_ifs
    · simp
    · rw [map_div₀, map_one, map_ofNat]
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · simp only [waveOp_core, map_add, map_sum, map_mul, hw]
  · simp [waveOp_dead]
  · induction x using Quotient.inductionOn with
    | h P =>
      change waveOp q _ (.neck (Branch.mk P)) = conj (waveOp q f (.neck (Branch.mk P)))
      rw [waveOp_neck, waveOp_neck]
      unfold neckOp
      split_ifs <;> simp
  · simp [waveOp_cap]
  · simp only [waveOp_ray_zero, map_add]
    unfold gapOp
    split_ifs <;> simp
  · simp [waveOp_ray_succ]

/-- The truncated sum is additive. -/
theorem truncSum_add (K : ℕ) (F H : Vertex G D → ℂ) :
    truncSum K (fun v => F v + H v) = truncSum K F + truncSum K H := by
  unfold truncSum
  simp only [Finset.sum_add_distrib, mul_add]
  have e : ∀ P : G, (if h : 2 • P = 0 then F (.cap ⟨P, h⟩) + H (.cap ⟨P, h⟩) else 0) =
      (if h : 2 • P = 0 then F (.cap ⟨P, h⟩) else 0) +
        (if h : 2 • P = 0 then H (.cap ⟨P, h⟩) else 0) := by
    intro P
    split_ifs <;> simp
  simp only [e, Finset.sum_add_distrib]
  ring

/-- The truncated sum is homogeneous. -/
theorem truncSum_smul (K : ℕ) (a : ℂ) (F : Vertex G D → ℂ) :
    truncSum K (fun v => a * F v) = a * truncSum K F := by
  unfold truncSum
  have e : ∀ P : G, (if h : 2 • P = 0 then a * F (.cap ⟨P, h⟩) else 0) =
      a * (if h : 2 • P = 0 then F (.cap ⟨P, h⟩) else 0) := by
    intro P
    split_ifs <;> simp
  have e2 : ∀ P : G, branchWeight P * (a * F (.neck (Branch.mk P))) =
      a * (branchWeight P * F (.neck (Branch.mk P))) := fun P => by ring
  simp only [e, e2, ← Finset.mul_sum]
  ring

theorem truncSum_congr (K : ℕ) {F H : Vertex G D → ℂ} (h : ∀ v, F v = H v) :
    truncSum K F = truncSum K H := by
  have : F = H := funext h
  rw [this]

theorem branchWeight_nonneg (P : G) : (0 : ℂ) ≤ branchWeight P := by
  unfold branchWeight
  split_ifs
  · exact zero_le_one
  · rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by norm_num)

/-- Nonnegativity of the truncated sum. -/
theorem truncSum_nonneg (K : ℕ) {F : Vertex G D → ℂ} (h : ∀ v, 0 ≤ F v) : 0 ≤ truncSum K F := by
  have hw := branchWeight_nonneg (G := G)
  unfold truncSum
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (h _) (Finset.sum_nonneg fun _ _ => h _))
    (Finset.sum_nonneg fun P _ => mul_nonneg (hw P) (h _))) (Finset.sum_nonneg fun P _ => ?_))
    (Finset.sum_nonneg fun P _ => Finset.sum_nonneg fun k _ => h _)
  split_ifs
  · exact h _
  · exact le_rfl

/-- The core mass is at most the truncated mass. -/
theorem core_le_truncSum (K : ℕ) {F : Vertex G D → ℂ} (h : ∀ v, 0 ≤ F v) :
    F .core ≤ truncSum K F := by
  have := truncSum_nonneg K (fun v => h v)
  have hsplit : truncSum K F = F .core + (∑ d, F (.dead d) +
      ∑ P : G, branchWeight P * F (.neck (Branch.mk P)) +
      ∑ P : G, (if h : 2 • P = 0 then F (.cap ⟨P, h⟩) else 0) +
      ∑ P : G, ∑ k ∈ range K, F (.ray P k)) := by
    unfold truncSum
    ring
  rw [hsplit]
  have hw := branchWeight_nonneg (G := G)
  have hrest : 0 ≤ ∑ d, F (.dead d) + ∑ P : G, branchWeight P * F (.neck (Branch.mk P)) +
      ∑ P : G, (if h : 2 • P = 0 then F (.cap ⟨P, h⟩) else 0) +
      ∑ P : G, ∑ k ∈ range K, F (.ray P k) := by
    refine add_nonneg (add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => h _)
      (Finset.sum_nonneg fun P _ => mul_nonneg (hw P) (h _))) (Finset.sum_nonneg fun P _ => ?_))
      (Finset.sum_nonneg fun P _ => Finset.sum_nonneg fun k _ => h _)
    split_ifs
    · exact h _
    · exact le_rfl
  exact le_add_of_nonneg_right hrest

/-- The measure is nonnegative. -/
theorem Channels.mass_nonneg (B : Channels G D) (v : Vertex G D) : (0 : ℂ) ≤ mass B.q v := by
  have hq : (2 : ℝ) ≤ B.q := by exact_mod_cast B.two_le
  have c1 : (0 : ℂ) ≤ ((((B.q : ℝ) + 1)⁻¹ : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (by positivity)
  have c2 : (0 : ℂ) ≤ ((((B.q : ℝ) - 1)⁻¹ : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (inv_nonneg.mpr (by linarith))
  have hk (k : ℕ) : (0 : ℂ) ≤ (((((B.q : ℝ) - 1) * (B.q : ℝ) ^ (k + 1))⁻¹ : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr
      (inv_nonneg.mpr (mul_nonneg (by linarith) (by positivity)))
  have hc : (0 : ℂ) ≤ ((((((B.q : ℝ) ^ 2 - 1) * B.q)⁻¹ : ℝ)) : ℂ) :=
    Complex.zero_le_real.mpr
      (inv_nonneg.mpr (mul_nonneg (by nlinarith) (by positivity)))
  rcases v with _ | d | x | L | ⟨P, k⟩
  · rw [mass_core]
    exact zero_le_one
  · simpa [mass_dead] using c1
  · induction x using Quotient.inductionOn with
    | h P =>
      change (0 : ℂ) ≤ mass B.q (.neck (Branch.mk P))
      rw [mass_neck]
      unfold neckMass
      split_ifs
      · simp
      · simpa using c2
  · simpa [mass_cap] using hc
  · simpa [mass_ray, rayMass] using hk k

/-- The mass of a ray: a geometric sum. -/
theorem sum_rayMass (q : ℕ) (hq : (q : ℂ) ≠ 0) (hq1 : (q : ℂ) - 1 ≠ 0) (K : ℕ) :
    ∑ k ∈ range K, rayMass q k = (1 - ((q : ℂ)⁻¹) ^ K) / ((q : ℂ) - 1) ^ 2 := by
  have huq : (q : ℂ)⁻¹ * q = 1 := inv_mul_cancel₀ hq
  induction K with
  | zero => simp
  | succ K ih =>
    have e : rayMass q K = ((q : ℂ)⁻¹) ^ (K + 1) / ((q : ℂ) - 1) := by
      unfold rayMass
      rw [inv_pow]
      field_simp
    have e2 (A B : ℂ) : A / ((q : ℂ) - 1) ^ 2 + B / ((q : ℂ) - 1) =
        (A + B * ((q : ℂ) - 1)) / ((q : ℂ) - 1) ^ 2 := by
      field_simp
    rw [Finset.sum_range_succ, ih, e, e2]
    congr 1
    linear_combination (((q : ℂ)⁻¹) ^ K) * huq

/-- **Finite volume.** The mass below depth `K` is the mass of the gap-zero part plus a convergent geometric sum, so
the black hole has finite volume, with cusps of mass `1/(q-1)²`. -/
theorem Channels.truncSum_mass (B : Channels G D) (K : ℕ) :
    truncSum K (mass B.q : Vertex G D → ℂ) = truncSum 0 (mass B.q : Vertex G D → ℂ) +
      cuspCount G * ((1 - ((B.q : ℂ)⁻¹) ^ K) / ((B.q : ℂ) - 1) ^ 2) := by
  have h := sum_rayMass B.q B.q_ne_zero B.q_sub_one_ne_zero K
  unfold truncSum
  simp only [mass_ray, Finset.sum_range_zero, Finset.sum_const_zero, add_zero, h, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, cuspCount]

/-- `z z̄` is nonnegative. -/
theorem mul_conj_nonneg (z : ℂ) : (0 : ℂ) ≤ z * conj z := by
  rw [Complex.mul_conj]
  exact Complex.zero_le_real.mpr (Complex.normSq_nonneg z)

/-- The mass density `μ |f|²`. -/
def massDensity (q : ℕ) (f : Vertex G D → ℂ) (v : Vertex G D) : ℂ := mass q v * (f v * conj (f v))

/-- The mass density is nonnegative. -/
theorem Channels.massDensity_nonneg (B : Channels G D) (f : Vertex G D → ℂ) (v : Vertex G D) :
    0 ≤ massDensity B.q f v :=
  mul_nonneg (B.mass_nonneg v) (mul_conj_nonneg _)

/-- **The flux law of an eigenfunction.** `(λ - λ̄) · mass below depth K + 1 = flux at K`. -/
theorem flux_law (B : Channels G D) {lam : ℂ} {f : Vertex G D → ℂ}
    (hf : ∀ v, waveOp B.q f v = lam * f v) (K : ℕ) :
    (lam - conj lam) * truncSum (K + 1) (massDensity B.q f) =
      ∑ P : G, rayFlux B.q f (fun w => conj (f w)) P K := by
  rw [← truncSum_greenDensity B f (fun w => conj (f w)) K, ← truncSum_smul]
  refine truncSum_congr _ fun v => ?_
  unfold greenDensity massDensity
  rw [waveOp_conj, hf]
  simp only [map_mul]
  ring

/-- The flux of an outgoing solution on one ray. -/
theorem rayFlux_outgoing {q : ℕ} {X Y : ℂ} {f : Vertex G D → ℂ} {c : G → ℂ}
    (hf : IsOutgoing q X Y f c) (P : G) (K : ℕ) :
    rayFlux q f (fun w => conj (f w)) P K =
      rayMass q K * (Complex.normSq (c P) * Complex.normSq Y ^ K : ℝ) * (Y - conj Y) := by
  unfold rayFlux
  simp only [hf.ray, map_mul, map_pow]
  have hc : c P * conj (c P) = (Complex.normSq (c P) : ℂ) := Complex.mul_conj _
  have hY : Y * conj Y = (Complex.normSq Y : ℂ) := Complex.mul_conj _
  push_cast
  rw [← hc, ← hY]
  ring

/-- The real amplitude sum `S = μ_K Σ_P |c_P|² |Y|^{2K}`. -/
def outgoingFlux (q : ℕ) (Y : ℂ) (c : G → ℂ) (K : ℕ) : ℝ :=
  (((q : ℝ) - 1) * (q : ℝ) ^ (K + 1))⁻¹ * ((∑ P, Complex.normSq (c P)) * Complex.normSq Y ^ K)

theorem rayMass_eq_ofReal (q K : ℕ) : rayMass q K = ((((q : ℝ) - 1) * (q : ℝ) ^ (K + 1))⁻¹ : ℝ) := by
  unfold rayMass
  push_cast
  rw [one_div]

/-- The real part of the mass of `f` below depth `K`. -/
def massBelow (q : ℕ) (f : Vertex G D → ℂ) (K : ℕ) : ℝ := (truncSum K (massDensity q f)).re

theorem Channels.massBelow_ofReal (B : Channels G D) (f : Vertex G D → ℂ) (K : ℕ) :
    (massBelow B.q f K : ℂ) = truncSum K (massDensity B.q f) := by
  have h := truncSum_nonneg K (B.massDensity_nonneg f)
  rw [Complex.nonneg_iff] at h
  apply Complex.ext
  · simp [massBelow]
  · simp [massBelow, h.2.symm]

theorem Channels.massBelow_nonneg (B : Channels G D) (f : Vertex G D → ℂ) (K : ℕ) :
    0 ≤ massBelow B.q f K := by
  have h := truncSum_nonneg K (B.massDensity_nonneg f)
  rw [Complex.nonneg_iff] at h
  exact h.1

/-- **The mass law.** For an outgoing solution with nonreal `Y`,
`(1 - q/|Y|²) · mass below depth K + 1 = μ_K Σ_P |c_P|² |Y|^{2K}`. -/
theorem mass_law (B : Channels G D) {X Y : ℂ} (hXY : X * Y = B.q) (hYim : Y.im ≠ 0)
    {f : Vertex G D → ℂ} {c : G → ℂ} (hf : IsOutgoing B.q X Y f c) (K : ℕ) :
    (1 - (B.q : ℝ) / Complex.normSq Y) * massBelow B.q f (K + 1) = outgoingFlux B.q Y c K := by
  have hYne : Y ≠ 0 := fun h => hYim (by simp [h])
  have hnY : Complex.normSq Y ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]
    exact hYne
  have hnY' : (Complex.normSq Y : ℂ) ≠ 0 := by exact_mod_cast hnY
  have hflux := flux_law B hf.eigen K
  rw [Finset.sum_congr rfl fun P _ => rayFlux_outgoing hf P K, ← B.massBelow_ofReal] at hflux
  have hsum : ∑ P : G, rayMass B.q K * (Complex.normSq (c P) * Complex.normSq Y ^ K : ℝ) *
      (Y - conj Y) = (outgoingFlux B.q Y c K : ℂ) * (Y - conj Y) := by
    unfold outgoingFlux
    rw [rayMass_eq_ofReal]
    push_cast
    rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  rw [hsum] at hflux
  have hX : X = (B.q : ℂ) * conj Y / (Complex.normSq Y : ℂ) := by
    rw [eq_div_iff hnY', ← Complex.mul_conj, ← hXY]
    ring
  have hconjX : conj X = (B.q : ℂ) * Y / (Complex.normSq Y : ℂ) := by
    rw [hX]
    simp [Complex.conj_ofReal]
  have hlam : (X + Y) - conj (X + Y) =
      ((1 - (B.q : ℝ) / Complex.normSq Y : ℝ) : ℂ) * (Y - conj Y) := by
    rw [map_add, hconjX]
    nth_rewrite 1 [hX]
    push_cast
    field_simp
    ring
  rw [hlam] at hflux
  have hsub : Y - conj Y ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    exact hYim (by linarith)
  have hcancel : ((1 - (B.q : ℝ) / Complex.normSq Y : ℝ) : ℂ) * (massBelow B.q f (K + 1) : ℂ) =
      (outgoingFlux B.q Y c K : ℂ) := by
    apply mul_right_cancel₀ hsub
    rw [← hflux]
    ring
  exact_mod_cast hcancel

/-- The flux of a nonzero amplitude is positive. -/
theorem outgoingFlux_pos (B : Channels G D) {Y : ℂ} (hY : Y ≠ 0) {c : G → ℂ} (hc : ∃ P, c P ≠ 0)
    (K : ℕ) : 0 < outgoingFlux B.q Y c K := by
  obtain ⟨P, hP⟩ := hc
  have hq : (2 : ℝ) ≤ B.q := by exact_mod_cast B.two_le
  have hs : 0 < ∑ P, Complex.normSq (c P) :=
    Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
      ⟨P, Finset.mem_univ _, Complex.normSq_pos.mpr hP⟩
  unfold outgoingFlux
  have h1 : 0 < ((B.q : ℝ) - 1) * (B.q : ℝ) ^ (K + 1) :=
    mul_pos (by linarith) (by positivity)
  have h2 : 0 < Complex.normSq Y := Complex.normSq_pos.mpr hY
  positivity

/-- **Causality from flux.** A nonreal resonance with a nonzero amplitude is damped: `|X|² < q`. -/
theorem normSq_lt_of_outgoing (B : Channels G D) {X Y : ℂ} (hXY : X * Y = B.q) (hYim : Y.im ≠ 0)
    {f : Vertex G D → ℂ} {c : G → ℂ} (hf : IsOutgoing B.q X Y f c) (hc : ∃ P, c P ≠ 0) :
    Complex.normSq X < B.q := by
  have hYne : Y ≠ 0 := fun h => hYim (by simp [h])
  have hq : (2 : ℝ) ≤ B.q := by exact_mod_cast B.two_le
  have hq0 : (0 : ℝ) < B.q := by linarith
  have hlaw := mass_law B hXY hYim hf 0
  have hpos := outgoingFlux_pos B hYne hc 0
  rw [← hlaw] at hpos
  have hM := B.massBelow_nonneg f 1
  have hfac : 0 < 1 - (B.q : ℝ) / Complex.normSq Y := by
    by_contra hneg
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hM
    linarith
  have hnY : 0 < Complex.normSq Y := Complex.normSq_pos.mpr hYne
  have hlt : (B.q : ℝ) < Complex.normSq Y := by
    rw [sub_pos, div_lt_one hnY] at hfac
    exact hfac
  have hprod : Complex.normSq X * Complex.normSq Y = (B.q : ℝ) ^ 2 := by
    rw [← Complex.normSq_mul, hXY, Complex.normSq_natCast]
    ring
  by_contra hge
  have hge' := not_lt.mp hge
  nlinarith

/-- **The core mass law.** The core mass of a nonreal resonant state, times the distance `|Y|²/q - 1` of
the mode from the unitary circle, is the amplitude. So the state becomes heavy as the mode nears the
circle. -/
theorem core_mass_law (B : Channels G D) {X Y : ℂ} (hXY : X * Y = B.q) (hYim : Y.im ≠ 0)
    {f : Vertex G D → ℂ} {c : G → ℂ} (hf : IsOutgoing B.q X Y f c) :
    (Complex.normSq Y / (B.q : ℝ) - 1) * massBelow B.q f 0 = outgoingFlux B.q Y c 0 := by
  have hYne : Y ≠ 0 := fun h => hYim (by simp [h])
  have hnY : Complex.normSq Y ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]
    exact hYne
  have hq : (2 : ℝ) ≤ B.q := by exact_mod_cast B.two_le
  have hq0 : (B.q : ℝ) ≠ 0 := by linarith
  have hlaw := mass_law B hXY hYim hf 0
  have hstep : massBelow B.q f (0 + 1) = massBelow B.q f 0 + outgoingFlux B.q Y c 0 := by
    have hsplit : truncSum (0 + 1) (massDensity B.q f) =
        truncSum 0 (massDensity B.q f) + ∑ P : G, massDensity B.q f (.ray P 0) := by
      unfold truncSum
      simp
    have hrays : ∑ P : G, massDensity B.q f (.ray P 0) = (outgoingFlux B.q Y c 0 : ℂ) := by
      unfold massDensity outgoingFlux
      simp only [mass_ray, hf.ray, pow_zero, mul_one, rayMass_eq_ofReal]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [Complex.mul_conj]
    have := congrArg Complex.re hsplit
    unfold massBelow
    rw [this, Complex.add_re, hrays, Complex.ofReal_re]
  rw [hstep] at hlaw
  field_simp at hlaw ⊢
  linarith

/-! ### Resonant states as model-space kernels -/

/-- **The Gram law.** Two outgoing solutions pair as a Szegő kernel: with `z = √q / Y`, the factor
`1 - q/(Y₁ Ȳ₂)` is `1 - z₁ z̄₂`, so the truncated resonant states are the reproducing kernels of a model space. -/
theorem gram_law (B : Channels G D) {X₁ Y₁ X₂ Y₂ : ℂ} (hXY₁ : X₁ * Y₁ = B.q) (hXY₂ : X₂ * Y₂ = B.q)
    (hne : Y₁ ≠ conj Y₂) {f₁ f₂ : Vertex G D → ℂ} {c₁ c₂ : G → ℂ} (h₁ : IsOutgoing B.q X₁ Y₁ f₁ c₁)
    (h₂ : IsOutgoing B.q X₂ Y₂ f₂ c₂) (K : ℕ) :
    (1 - (B.q : ℂ) / (Y₁ * conj Y₂)) * truncSum (K + 1) (fun v => mass B.q v * (f₁ v * conj (f₂ v))) =
      rayMass B.q K * (∑ P, c₁ P * conj (c₂ P)) * (Y₁ * conj Y₂) ^ K := by
  have hq0 := B.q_ne_zero
  have hY₁ : Y₁ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hXY₁
    exact hq0 hXY₁.symm
  have hY₂ : Y₂ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hXY₂
    exact hq0 hXY₂.symm
  have hY₂c : conj Y₂ ≠ 0 := by
    rwa [Ne, map_eq_zero]
  have hgreen := truncSum_greenDensity B f₁ (fun w => conj (f₂ w)) K
  have hdens : truncSum (K + 1) (greenDensity B.q f₁ fun w => conj (f₂ w)) =
      ((X₁ + Y₁) - conj (X₂ + Y₂)) *
        truncSum (K + 1) (fun v => mass B.q v * (f₁ v * conj (f₂ v))) := by
    rw [← truncSum_smul]
    refine truncSum_congr _ fun v => ?_
    unfold greenDensity
    rw [waveOp_conj, h₁.eigen, h₂.eigen]
    simp only [map_mul]
    ring
  have hflux : ∑ P : G, rayFlux B.q f₁ (fun w => conj (f₂ w)) P K =
      rayMass B.q K * (∑ P, c₁ P * conj (c₂ P)) * (Y₁ * conj Y₂) ^ K * (Y₁ - conj Y₂) := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun P _ => ?_
    unfold rayFlux
    simp only [h₁.ray, h₂.ray, map_mul, map_pow]
    rw [mul_pow]
    ring
  rw [hdens, hflux] at hgreen
  have hX₁ : X₁ = (B.q : ℂ) / Y₁ := by
    rw [eq_div_iff hY₁]
    exact hXY₁
  have hX₂c : conj X₂ = (B.q : ℂ) / conj Y₂ := by
    have : X₂ = (B.q : ℂ) / Y₂ := by
      rw [eq_div_iff hY₂]
      exact hXY₂
    rw [this]
    simp
  have hfactor : (X₁ + Y₁) - conj (X₂ + Y₂) =
      (1 - (B.q : ℂ) / (Y₁ * conj Y₂)) * (Y₁ - conj Y₂) := by
    rw [map_add, hX₂c, hX₁]
    field_simp
    ring
  rw [hfactor] at hgreen
  have hsub : Y₁ - conj Y₂ ≠ 0 := sub_ne_zero.mpr hne
  apply mul_right_cancel₀ hsub
  linear_combination hgreen

/-! ### Energy balance -/

/-- The sesquilinear pairing on the part of the graph below depth `K`. -/
def pairing (q K : ℕ) (f g : Vertex G D → ℂ) : ℂ :=
  truncSum K fun v => mass q v * (f v * conj (g v))

theorem pairing_add_left (q K : ℕ) (f f' g : Vertex G D → ℂ) :
    pairing q K (fun v => f v + f' v) g = pairing q K f g + pairing q K f' g := by
  unfold pairing
  rw [← truncSum_add]
  refine truncSum_congr _ fun v => ?_
  ring

theorem pairing_smul_left (q K : ℕ) (a : ℂ) (f g : Vertex G D → ℂ) :
    pairing q K (fun v => a * f v) g = a * pairing q K f g := by
  unfold pairing
  rw [← truncSum_smul]
  refine truncSum_congr _ fun v => ?_
  ring

theorem pairing_add_right (q K : ℕ) (f g g' : Vertex G D → ℂ) :
    pairing q K f (fun v => g v + g' v) = pairing q K f g + pairing q K f g' := by
  unfold pairing
  rw [← truncSum_add]
  refine truncSum_congr _ fun v => ?_
  rw [map_add]
  ring

theorem pairing_natCast_smul_right (q K n : ℕ) (f g : Vertex G D → ℂ) :
    pairing q K f (fun v => (n : ℂ) * g v) = (n : ℂ) * pairing q K f g := by
  unfold pairing
  rw [← truncSum_smul]
  refine truncSum_congr _ fun v => ?_
  rw [map_mul, Complex.conj_natCast]
  ring

/-- The leapfrog energy of a pair of waves, normalized by `q^{-τ}`. -/
def energy (q K : ℕ) (u w : ℤ → Vertex G D → ℂ) (τ : ℤ) : ℂ :=
  (q : ℂ) ^ (-(τ + 1)) * pairing q K (u (τ + 1)) (w (τ + 1)) +
    (q : ℂ) ^ (-τ) * pairing q K (u τ) (w τ) -
    (q : ℂ) ^ (-(τ + 1)) * pairing q K (waveOp q (u (τ + 1))) (w τ)

/-- **Energy balance.** For any two waves, the energy below depth `K + 1` changes in one tick exactly by
the flux through the cusps. If one wave vanishes near the boundary, the energy is conserved. -/
theorem energy_balance (B : Channels G D) {u w : ℤ → Vertex G D → ℂ} (hu : IsWave B.q u)
    (hw : IsWave B.q w) (K : ℕ) (τ : ℤ) :
    energy B.q (K + 1) u w τ - energy B.q (K + 1) u w (τ + (-1)) =
      -((B.q : ℂ) ^ (-(τ + 1)) *
        ∑ P : G, rayFlux B.q (u (τ + 1)) (fun v => conj (w τ v)) P K) := by
  have hq0 := B.q_ne_zero
  have hgreen := truncSum_greenDensity B (u (τ + 1)) (fun v => conj (w τ v)) K
  have hexp : truncSum (K + 1) (greenDensity B.q (u (τ + 1)) fun v => conj (w τ v)) =
      pairing B.q (K + 1) (waveOp B.q (u (τ + 1))) (w τ) -
        pairing B.q (K + 1) (u (τ + 1)) (waveOp B.q (w τ)) := by
    unfold pairing
    have hneg : pairing B.q (K + 1) (u (τ + 1)) (waveOp B.q (w τ)) =
        pairing B.q (K + 1) (u (τ + 1)) (waveOp B.q (w τ)) := rfl
    have hsub : ∀ F H : Vertex G D → ℂ, truncSum (K + 1) (fun v => F v - H v) =
        truncSum (K + 1) F - truncSum (K + 1) H := by
      intro F H
      have h1 := truncSum_add (K + 1) F (fun v => (-1 : ℂ) * H v)
      rw [truncSum_smul] at h1
      have h2 : (fun v => F v - H v) = fun v => F v + (-1 : ℂ) * H v := by
        funext v
        ring
      rw [h2, h1]
      ring
    rw [← hsub]
    refine truncSum_congr _ fun v => ?_
    unfold greenDensity
    rw [waveOp_conj]
    ring
  have hAw : waveOp B.q (w τ) = fun v => w (τ + 1) v + (B.q : ℂ) * w (τ + (-1)) v :=
    funext fun v => (hw τ v).symm
  have hAu : waveOp B.q (u τ) = fun v => u (τ + 1) v + (B.q : ℂ) * u (τ + (-1)) v :=
    funext fun v => (hu τ v).symm
  have hP1 : pairing B.q (K + 1) (u (τ + 1)) (waveOp B.q (w τ)) =
      pairing B.q (K + 1) (u (τ + 1)) (w (τ + 1)) +
        (B.q : ℂ) * pairing B.q (K + 1) (u (τ + 1)) (w (τ + (-1))) := by
    rw [hAw, pairing_add_right, pairing_natCast_smul_right]
  have hP2 : pairing B.q (K + 1) (waveOp B.q (u τ)) (w (τ + (-1))) =
      pairing B.q (K + 1) (u (τ + 1)) (w (τ + (-1))) +
        (B.q : ℂ) * pairing B.q (K + 1) (u (τ + (-1))) (w (τ + (-1))) := by
    rw [hAu, pairing_add_left, pairing_smul_left]
  rw [hexp] at hgreen
  unfold energy
  have ei : τ + (-1) + 1 = τ := by ring
  rw [ei]
  have p1 : (B.q : ℂ) ^ (-τ) = (B.q : ℂ) ^ (-(τ + 1)) * (B.q : ℂ) := by
    rw [← zpow_add_one₀ hq0]
    congr 1
    ring
  have p2 : (B.q : ℂ) ^ (-(τ + (-1))) = (B.q : ℂ) ^ (-(τ + 1)) * (B.q : ℂ) * (B.q : ℂ) := by
    rw [mul_assoc, ← pow_two, ← zpow_natCast, ← zpow_add₀ hq0]
    congr 1
    push_cast
    ring
  rw [p1, p2]
  linear_combination -((B.q : ℂ) ^ (-(τ + 1))) * hgreen - ((B.q : ℂ) ^ (-(τ + 1))) * hP1 +
    ((B.q : ℂ) ^ (-(τ + 1)) * (B.q : ℂ)) * hP2

end GaloisForLFunctions.ArithmeticScatteringHolography

end
