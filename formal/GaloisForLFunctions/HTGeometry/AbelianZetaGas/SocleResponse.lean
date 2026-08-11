import Mathlib
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GrandResponse

/-!
# The socle response and its translation transgression

The generated fugacity intervention acts in the socle direction: it translates `τ`.  Its response
is the normalized depth product

`C_{σ,τ}(z) = ∏_{j≥1} ζ(jσ + τ + z) / ∏_{j≥1} ζ(jσ + τ)`,

which in the vocabulary of the dilation organ is `grandResponse σ (τ + z) 0 / grandResponse σ τ 0`.

Peeling the first depth factor gives the exact one-step ladder `Z(σ,v) = ζ(σ+v) · Z(σ, v+σ)`.
Hence translating the response by one temperature divides it by a single zeta value: the
translation transgression.  The normalizer is nonzero throughout the convergence chamber, so the
response is a genuine normalized intervention there.
-/

namespace GaloisForLFunctions.HTGeometry.AbelianZetaGas

noncomputable section

/-- The complete depth product in the socle variable, `Z(σ, v) = ∏_{j≥1} ζ(jσ + v)`. -/
def socleLadder (σ : ℝ) (v : ℂ) : ℂ := grandResponse σ v 0

theorem socleLadder_eq_tprod (σ : ℝ) (v : ℂ) :
    socleLadder σ v = ∏' j : ℕ, riemannZeta (((j + 1 : ℕ) : ℂ) * (σ : ℂ) + v) := by
  rw [socleLadder, grandResponse]
  refine tprod_congr (fun j => ?_)
  rw [depthFactor_eq_zeta_depthArg, depthArg]
  norm_num

theorem multipliable_socleLadder {σ : ℝ} (hσ : 0 < σ) (v : ℂ) :
    Multipliable fun j : ℕ => depthFactor σ v (j + 1) 0 :=
  multipliable_depthFactor_succ σ v (by simpa using hσ)

theorem multipliable_socleLadder_shift {σ : ℝ} (hσ : 0 < σ) (v : ℂ) (k : ℕ) :
    Multipliable fun j : ℕ => depthFactor σ v (j + k) 0 :=
  multipliable_depthFactor_shift σ v (by simpa using hσ) k

/-- **The socle ladder telescopes.**  Peeling the first depth factor divides the depth product by
one zeta value and shifts the socle parameter by one temperature. -/
theorem socleLadder_peel {σ : ℝ} (hσ : 0 < σ) (v : ℂ) :
    socleLadder σ v = riemannZeta ((σ : ℂ) + v) * socleLadder σ (v + (σ : ℂ)) := by
  have hshift : Multipliable fun n : ℕ => depthFactor σ v (n + 1 + 1) 0 := by
    have h := multipliable_socleLadder_shift hσ v 2
    exact h.congr (fun n => by rw [show n + 1 + 1 = n + 2 from rfl])
  have hsplit := tprod_split_nat (multipliable_socleLadder hσ v) 1 hshift
  rw [socleLadder, grandResponse, hsplit]
  congr 1
  · rw [Finset.prod_range_one, depthFactor_eq_zeta_depthArg, depthArg]
    norm_num
  · rw [socleLadder, grandResponse]
    refine tprod_congr (fun n => ?_)
    rw [depthFactor_eq_zeta_depthArg, depthFactor_eq_zeta_depthArg, depthArg, depthArg]
    push_cast
    ring_nf

/-- The finite head of the socle ladder is nonzero to the right of the first depth line. -/
theorem depthProduct_socle_ne_zero {σ τ : ℝ} (hσ : 0 < σ) (hτ : 1 < σ + τ) (J : ℕ) :
    depthProduct σ ((τ : ℝ) : ℂ) J 0 ≠ 0 := by
  rw [depthProduct]
  refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
  rw [depthFactor_eq_zeta_depthArg]
  refine riemannZeta_ne_zero_of_one_lt_re ?_
  rw [re_depthArg]
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have h0 : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) - 1 := by linarith
  simp only [Complex.zero_re, add_zero, Complex.ofReal_re]
  nlinarith

/-- **The normalizer is nonzero on the convergence chamber.** -/
theorem socleLadder_ne_zero {σ τ : ℝ} (hσ : 0 < σ) (hτ : 1 < σ + τ) :
    socleLadder σ ((τ : ℝ) : ℂ) ≠ 0 := by
  set J : ℕ := depthTailThreshold ((τ : ℝ) : ℂ) σ with hJ
  have ha : (0 : ℝ) < σ + (0 : ℂ).re := by simpa using hσ
  have hsplit := grandResponse_split σ ((τ : ℝ) : ℂ) ha J
  have htail : (∏' j : ℕ, depthFactor σ ((τ : ℝ) : ℂ) (j + (J + 1)) 0) ≠ 0 :=
    tprod_depthFactor_tail_ne_zero σ ((τ : ℝ) : ℂ) hσ (by simp)
      (le_trans (le_of_eq hJ.symm) (Nat.le_succ J))
  rw [socleLadder, hsplit]
  exact mul_ne_zero (depthProduct_socle_ne_zero hσ hτ J) htail

/-- The normalized socle response of the gas. -/
def socleResponse (σ τ : ℝ) (z : ℂ) : ℂ :=
  socleLadder σ ((τ : ℂ) + z) / socleLadder σ (τ : ℂ)

theorem socleResponse_zero {σ τ : ℝ} (hσ : 0 < σ) (hτ : 1 < σ + τ) :
    socleResponse σ τ 0 = 1 := by
  rw [socleResponse, add_zero]
  exact div_self (socleLadder_ne_zero hσ hτ)

/-- **Translation transgression, multiplicative form.**  Translating the socle parameter by one
temperature costs exactly one zeta value. -/
theorem socleLadder_translation {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) (z : ℂ) :
    riemannZeta ((σ : ℂ) + ((τ : ℂ) + z)) * socleLadder σ ((τ : ℂ) + z + (σ : ℂ))
      = socleLadder σ ((τ : ℂ) + z) :=
  (socleLadder_peel hσ ((τ : ℂ) + z)).symm

/-- **Translation transgression for the response.**  The response translated by one temperature is
the response divided by a single zeta value. -/
theorem socleResponse_translation {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) (z : ℂ) :
    riemannZeta ((σ : ℂ) + (τ : ℂ) + z) * socleResponse σ τ (z + (σ : ℂ))
      = socleResponse σ τ z := by
  rw [socleResponse, socleResponse, ← mul_div_assoc]
  congr 1
  have hz : (τ : ℂ) + (z + (σ : ℂ)) = (τ : ℂ) + z + (σ : ℂ) := by ring
  rw [hz, show (σ : ℂ) + (τ : ℂ) + z = (σ : ℂ) + ((τ : ℂ) + z) by ring]
  exact socleLadder_translation hσ τ z

/-- **The response quotient is the reciprocal zeta value.**  This is the division form of the
translation transgression on the locus where the response does not vanish. -/
theorem socleResponse_div {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) (z : ℂ)
    (hz : socleResponse σ τ z ≠ 0) (hζ : riemannZeta ((σ : ℂ) + (τ : ℂ) + z) ≠ 0) :
    socleResponse σ τ (z + (σ : ℂ)) / socleResponse σ τ z
      = 1 / riemannZeta ((σ : ℂ) + (τ : ℂ) + z) := by
  have h := socleResponse_translation hσ τ z
  field_simp
  linear_combination h

end

namespace SocleTail

open GaloisForLFunctions.HTGeometry.AbelianZetaGas

noncomputable section

/-- The uniform depth threshold on a socle half-plane `b ≤ Re v`. -/
def socleTailThreshold (σ b : ℝ) : ℕ := ⌈(2 - b) / σ⌉₊

theorem re_socleArg (σ : ℝ) (v : ℂ) (j : ℕ) :
    (depthArg σ v j 0).re = (j : ℝ) * σ + v.re := by
  rw [re_depthArg]
  simp

theorem two_le_re_socleArg {σ b : ℝ} (hσ : 0 < σ) {v : ℂ} (hv : b ≤ v.re) {j : ℕ}
    (hj : socleTailThreshold σ b ≤ j) : 2 ≤ (depthArg σ v j 0).re := by
  rw [re_socleArg]
  have hceil : (2 - b) / σ ≤ (j : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
  have hmul := (div_le_iff₀ hσ).mp hceil
  linarith

theorem norm_zeta_socleArg_sub_one_le {σ b : ℝ} (hσ : 0 < σ) {v : ℂ} (hv : b ≤ v.re) {j : ℕ}
    (hj : socleTailThreshold σ b ≤ j) :
    ‖riemannZeta (depthArg σ v j 0) - 1‖ ≤ 4 * (((2 : ℝ) ^ (-σ)) ^ j * (2 : ℝ) ^ (-b)) := by
  have hre := two_le_re_socleArg hσ hv hj
  have hbound := norm_riemannZeta_sub_one_le_rpow hre
  have hexp : -(depthArg σ v j 0).re ≤ -((j : ℝ) * σ + b) := by
    rw [re_socleArg]
    linarith
  have hmono : (2 : ℝ) ^ (-(depthArg σ v j 0).re) ≤ (2 : ℝ) ^ (-((j : ℝ) * σ + b)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hsplit : (2 : ℝ) ^ (-((j : ℝ) * σ + b))
      = ((2 : ℝ) ^ (-σ)) ^ j * (2 : ℝ) ^ (-b) := by
    rw [neg_add, Real.rpow_add (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-σ)) j,
      ← Real.rpow_mul (by norm_num)]
    congr 2
    ring
  calc ‖riemannZeta (depthArg σ v j 0) - 1‖ ≤ 4 * (2 : ℝ) ^ (-(depthArg σ v j 0).re) := hbound
    _ ≤ 4 * (2 : ℝ) ^ (-((j : ℝ) * σ + b)) := by linarith [hmono]
    _ = 4 * (((2 : ℝ) ^ (-σ)) ^ j * (2 : ℝ) ^ (-b)) := by rw [hsplit]

theorem differentiableAt_zeta_socleArg {σ b : ℝ} (hσ : 0 < σ) {v : ℂ} (hv : b ≤ v.re) {j : ℕ}
    (hj : socleTailThreshold σ b ≤ j) :
    DifferentiableAt ℂ (fun w : ℂ => riemannZeta (depthArg σ w j 0)) v := by
  have hre := two_le_re_socleArg hσ hv hj
  have hne : depthArg σ v j 0 ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
  have haff : DifferentiableAt ℂ (fun w : ℂ => depthArg σ w j 0) v := by
    show DifferentiableAt ℂ (fun w : ℂ => (j : ℂ) * ((σ : ℝ) + (0 : ℂ)) + w) v
    exact (differentiableAt_const _).add differentiableAt_id
  exact (differentiableAt_riemannZeta hne).comp v haff

/-- **The socle tail converges uniformly on every compact of the half-plane.** -/
theorem hasProdUniformlyOn_zeta_socleTail {σ b : ℝ} (hσ : 0 < σ) {J : ℕ}
    (hJthr : socleTailThreshold σ b ≤ J) {K : Set ℂ} (hKsub : K ⊆ {v : ℂ | b ≤ v.re})
    (hK : IsCompact K) :
    HasProdUniformlyOn
      (fun j : ℕ => fun v : ℂ => riemannZeta (depthArg σ v (j + J) 0))
      (fun v : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ v (j + J) 0)) K := by
  have hmaj : Summable fun j : ℕ =>
      4 * (((2 : ℝ) ^ (-σ)) ^ (j + J) * (2 : ℝ) ^ (-b)) := by
    refine Summable.mul_left 4 ?_
    refine Summable.mul_right _ ?_
    exact ((summable_geometric_of_lt_one (geomRatio_nonneg _)
      (geomRatio_lt_one hσ)).comp_injective (add_left_injective J))
  have hbound : ∀ᶠ j : ℕ in Filter.cofinite, ∀ v ∈ K,
      ‖riemannZeta (depthArg σ v (j + J) 0) - 1‖
        ≤ 4 * (((2 : ℝ) ^ (-σ)) ^ (j + J) * (2 : ℝ) ^ (-b)) := by
    filter_upwards with j
    intro v hv
    exact norm_zeta_socleArg_sub_one_le hσ (hKsub hv)
      (le_trans hJthr (Nat.le_add_left J j))
  have hcont : ∀ j : ℕ,
      ContinuousOn (fun v : ℂ => riemannZeta (depthArg σ v (j + J) 0) - 1) K := by
    intro j
    refine ContinuousOn.sub ?_ continuousOn_const
    intro v hv
    exact ((differentiableAt_zeta_socleArg hσ (hKsub hv)
      (le_trans hJthr (Nat.le_add_left J j))).continuousAt).continuousWithinAt
  have hmain := Summable.hasProdUniformlyOn_one_add hK hmaj hbound hcont
  have hfun : (fun (j : ℕ) (v : ℂ) => 1 + (riemannZeta (depthArg σ v (j + J) 0) - 1))
      = fun (j : ℕ) (v : ℂ) => riemannZeta (depthArg σ v (j + J) 0) := by
    funext j v
    ring
  have hval : (fun v : ℂ => ∏' j : ℕ, (1 + (riemannZeta (depthArg σ v (j + J) 0) - 1)))
      = fun v : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ v (j + J) 0) := by
    funext v
    exact tprod_congr fun j => by ring
  rw [hfun, hval] at hmain
  exact hmain

/-- **The socle tail product is holomorphic on the half-plane.** -/
theorem differentiableOn_tprod_zeta_socleTail {σ b : ℝ} (hσ : 0 < σ) {J : ℕ}
    (hJthr : socleTailThreshold σ b ≤ J) :
    DifferentiableOn ℂ
      (fun v : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ v (j + J) 0))
      {v : ℂ | b < v.re} := by
  have hopen : IsOpen {v : ℂ | b < v.re} := by
    have hcont : Continuous fun v : ℂ => v.re := Complex.continuous_re
    exact isOpen_lt continuous_const hcont
  have hprod : HasProdLocallyUniformlyOn
      (fun j : ℕ => fun v : ℂ => riemannZeta (depthArg σ v (j + J) 0))
      (fun v : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ v (j + J) 0))
      {v : ℂ | b < v.re} := by
    refine hasProdLocallyUniformlyOn_of_forall_compact hopen ?_
    intro K hKsub hK
    refine hasProdUniformlyOn_zeta_socleTail hσ hJthr (fun v hv => ?_) hK
    have hlt : b < v.re := hKsub hv
    exact le_of_lt hlt
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod
  have hd : ∀ᶠ S : Finset ℕ in Filter.atTop,
      DifferentiableOn ℂ (fun v : ℂ =>
        ∏ j ∈ S, riemannZeta (depthArg σ v (j + J) 0))
        {v : ℂ | b < v.re} := by
    filter_upwards with S
    refine DifferentiableOn.fun_finsetProd fun j _ => ?_
    intro v hv
    exact ((differentiableAt_zeta_socleArg hσ (le_of_lt hv)
      (le_trans hJthr (Nat.le_add_left J j))).differentiableWithinAt)
  exact ht.differentiableOn hd hopen

/-- **The socle tail is zero-free on the half-plane.** -/
theorem tprod_zeta_socleTail_ne_zero {σ b : ℝ} (hσ : 0 < σ) {J : ℕ}
    (hJthr : socleTailThreshold σ b ≤ J) {v : ℂ} (hv : b ≤ v.re) :
    (∏' j : ℕ, riemannZeta (depthArg σ v (j + J) 0)) ≠ 0 := by
  have hsum : Summable fun j : ℕ => ‖riemannZeta (depthArg σ v (j + J) 0) - 1‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => norm_zeta_socleArg_sub_one_le hσ hv (le_trans hJthr (Nat.le_add_left J j))) ?_
    refine Summable.mul_left 4 ?_
    refine Summable.mul_right _ ?_
    exact ((summable_geometric_of_lt_one (geomRatio_nonneg _)
      (geomRatio_lt_one hσ)).comp_injective (add_left_injective J))
  have hval : (∏' j : ℕ, riemannZeta (depthArg σ v (j + J) 0))
      = ∏' j : ℕ, (1 + (riemannZeta (depthArg σ v (j + J) 0) - 1)) :=
    tprod_congr fun j => by ring
  rw [hval]
  refine tprod_one_add_ne_zero_of_summable ?_ hsum
  intro j
  have hre := two_le_re_socleArg hσ hv (le_trans hJthr (Nat.le_add_left J j))
  have hne : riemannZeta (depthArg σ v (j + J) 0) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by linarith)
  intro h0
  apply hne
  have hid : (1 : ℂ) + (riemannZeta (depthArg σ v (j + J) 0) - 1)
      = riemannZeta (depthArg σ v (j + J) 0) := by ring
  rw [hid] at h0
  exact h0


end

end SocleTail

noncomputable section

/-! ## The socle chamber: holomorphy and zero-freeness of the ladder -/

/-- The socle chamber: the half-plane on which every depth argument has real part above one. -/
def socleChamber (σ : ℝ) : Set ℂ := {v : ℂ | 1 - σ < v.re}

theorem isOpen_socleChamber (σ : ℝ) : IsOpen (socleChamber σ) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem socleLadder_split {σ : ℝ} (hσ : 0 < σ) (v : ℂ) (J : ℕ) :
    socleLadder σ v
      = depthProduct σ v J 0 * ∏' j : ℕ, riemannZeta (depthArg σ v (j + J + 1) 0) := by
  have ha : (0 : ℝ) < σ + (0 : ℂ).re := by simpa using hσ
  have h := grandResponse_split σ v ha J
  rw [socleLadder, h]
  rfl

theorem depthProduct_ne_zero_of_lt_re {σ b : ℝ} (hσ : 0 < σ) (hb : 1 - σ < b) {v : ℂ}
    (hv : b ≤ v.re) (J : ℕ) : depthProduct σ v J 0 ≠ 0 := by
  rw [depthProduct]
  refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
  rw [depthFactor_eq_zeta_depthArg]
  refine riemannZeta_ne_zero_of_one_lt_re ?_
  rw [SocleTail.re_socleArg]
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  nlinarith

theorem differentiableOn_depthProduct {σ b : ℝ} (hσ : 0 < σ) (hb : 1 - σ < b) (J : ℕ) :
    DifferentiableOn ℂ (fun v : ℂ => depthProduct σ v J 0) {v : ℂ | b < v.re} := by
  refine DifferentiableOn.fun_finsetProd fun j _ => ?_
  intro v hv
  have hre : 1 < (depthArg σ v (j + 1) 0).re := by
    rw [SocleTail.re_socleArg]
    have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    have hvre : b < v.re := hv
    nlinarith
  have hne : depthArg σ v (j + 1) 0 ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
  have haff : DifferentiableAt ℂ (fun w : ℂ => depthArg σ w (j + 1) 0) v := by
    show DifferentiableAt ℂ (fun w : ℂ => ((j + 1 : ℕ) : ℂ) * ((σ : ℝ) + (0 : ℂ)) + w) v
    exact (differentiableAt_const _).add differentiableAt_id
  exact (((differentiableAt_riemannZeta hne).comp v haff)).differentiableWithinAt

set_option maxHeartbeats 1000000 in
/-- **The socle ladder is zero-free on the socle chamber.** -/
theorem socleLadder_ne_zero_of_mem {σ : ℝ} (hσ : 0 < σ) {v : ℂ} (hv : v ∈ socleChamber σ) :
    socleLadder σ v ≠ 0 := by
  have hb : 1 - σ < v.re := hv
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, SocleTail.socleTailThreshold σ v.re ≤ J := ⟨_, le_rfl⟩
  rw [socleLadder_split hσ v J]
  refine mul_ne_zero (depthProduct_ne_zero_of_lt_re hσ hb le_rfl J) ?_
  exact SocleTail.tprod_zeta_socleTail_ne_zero (J := J + 1) hσ
    (le_trans hJ (Nat.le_succ J)) le_rfl

set_option maxHeartbeats 1000000 in
/-- **The socle ladder is holomorphic on the socle chamber.** -/
theorem differentiableOn_socleLadder {σ : ℝ} (hσ : 0 < σ) :
    DifferentiableOn ℂ (socleLadder σ) (socleChamber σ) := by
  intro v hv
  have hb : 1 - σ < v.re := hv
  set b : ℝ := (1 - σ + v.re) / 2 with hbdef
  have hb1 : 1 - σ < b := by rw [hbdef]; linarith
  have hb2 : b < v.re := by rw [hbdef]; linarith
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, SocleTail.socleTailThreshold σ b ≤ J := ⟨_, le_rfl⟩
  have hopen : IsOpen {w : ℂ | b < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ => depthProduct σ w J 0 * ∏' j : ℕ, riemannZeta (depthArg σ w (j + J + 1) 0))
      {w : ℂ | b < w.re} := by
    refine DifferentiableOn.mul (differentiableOn_depthProduct hσ hb1 J) ?_
    exact SocleTail.differentiableOn_tprod_zeta_socleTail (J := J + 1) hσ
      (le_trans hJ (Nat.le_succ J))
  have hdiff' : DifferentiableOn ℂ (socleLadder σ) {w : ℂ | b < w.re} :=
    hdiff.congr (fun w _ => socleLadder_split hσ w J)
  exact ((hdiff' v hb2).differentiableAt (hopen.mem_nhds hb2)).differentiableWithinAt

end

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
