import GaloisForLFunctions.HyperbolicArakelovTheory.TheLocalGreenKernelOnAdelicVertices
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The prime walk selects the Green kernel

The actual uniform neighbour walk has the harmonic local kernel as its
convergent occupation sum. A tempered supersolution gives a geometric
remainder bound, and finite-walk comparison proves minimality among all
nonnegative supersolutions. The harmonic diagonal excess is the total
return mass after time zero.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeWalk
open FullAdelic AdelicAdjacency AdelicRadial AdelicGreen

variable (p : {p : ℕ // p.Prime})

private theorem degree_pos : 0 < (p.1 : ℝ) + 1 := by positivity

/-- Uniform averaging over the actual `p+1` neighbouring lattice classes. -/
def walkStep : Module.End ℝ (LocalVertex p → ℝ) where
  toFun f y := (∑ w ∈ neighbors p y, f w) / ((p.1 : ℝ) + 1)
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, Finset.sum_add_distrib, add_div]
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum,
      mul_div_assoc]

theorem walkStep_mono : Monotone (walkStep p) := by
  intro f g h y
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun w _ => h w) (degree_pos p).le

theorem walkStep_one : walkStep p (fun _ => 1) = fun _ => 1 := by
  funext y
  change (∑ _ ∈ neighbors p y, (1 : ℝ)) / ((p.1 : ℝ) + 1) = 1
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_neighbors, Nat.cast_add,
    Nat.cast_one, div_self (degree_pos p).ne']

/-- Finite walk powers preserve pointwise order. -/
theorem walkIter_mono (N : ℕ) : Monotone ((walkStep p) ^ N) := by
  induction N with
  | zero => intro f g h; exact h
  | succ N ih =>
      intro f g h y
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      exact walkStep_mono p (ih h) y

/-- Finite walk powers preserve nonnegativity. -/
theorem walkIter_nonneg (N : ℕ) {f : LocalVertex p → ℝ}
    (hf : ∀ y, 0 ≤ f y) (y : LocalVertex p) : 0 ≤ ((walkStep p) ^ N) f y := by
  have h := walkIter_mono p N (show (0 : LocalVertex p → ℝ) ≤ f from hf) y
  simpa only [map_zero, Pi.zero_apply] using h

/-- Unit mass at a target vertex. -/
def pointMass (x : LocalVertex p) (y : LocalVertex p) : ℝ := if x = y then 1 else 0

/-- Probability of reaching `x` from `y` after `N` uniform neighbour steps. -/
def walkMass (N : ℕ) (x y : LocalVertex p) : ℝ :=
  ((walkStep p) ^ N) (pointMass p x) y

theorem walkMass_nonneg (N : ℕ) (x y : LocalVertex p) : 0 ≤ walkMass p N x y := by
  apply walkIter_nonneg
  intro z
  simp only [pointMass]
  split_ifs <;> norm_num

theorem walkMass_le_one (N : ℕ) (x y : LocalVertex p) : walkMass p N x y ≤ 1 := by
  have hconst : ((walkStep p) ^ N) (fun _ => 1) = fun _ => 1 := by
    induction N with
    | zero => simp only [pow_zero, Module.End.one_apply]
    | succ N ih => rw [pow_succ', Module.End.mul_apply, ih, walkStep_one]
  have hsource : pointMass p x ≤ fun _ => 1 := by
    intro z
    simp only [pointMass]
    split_ifs <;> norm_num
  have h := walkIter_mono p N hsource y
  rw [hconst] at h
  exact h

/-- Tempered-to-harmonic spectral ratio, strictly below one at every prime. -/
def spectralRatio : ℝ := 2 * Real.sqrt p.1 / ((p.1 : ℝ) + 1)

theorem spectralRatio_nonneg : 0 ≤ spectralRatio p := by
  exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (degree_pos p).le

theorem spectralRatio_lt_one : spectralRatio p < 1 := by
  have hp : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ p.1 by positivity)
  have hn : Real.sqrt p.1 - 1 ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [he] at hs
    norm_num at hs
    exact hp.ne hs
  apply (div_lt_one (degree_pos p)).mpr
  nlinarith only [hs, sq_pos_of_ne_zero hn]

private theorem harmonic_source (x y : LocalVertex p) :
    ((p.1 : ℝ) + 1) * localGreen p 1 x y -
      (∑ w ∈ neighbors p y, localGreen p 1 x w) = pointMass p x y := by
  simpa only [treeEigen, Real.rpow_one, sub_self, Real.rpow_zero, pointMass] using
    localGreen_resolvent p (s := 1) zero_lt_one x y

private theorem tempered_step_le (x y : LocalVertex p) :
    walkStep p (localGreen p (1 / 2) x) y ≤
      spectralRatio p * localGreen p (1 / 2) x y := by
  have h := localGreen_tempered_resolvent p x y
  have hsource : (0 : ℝ) ≤ if x = y then 1 else 0 := by split_ifs <;> norm_num
  have hsum : (∑ w ∈ neighbors p y, localGreen p (1 / 2) x w) ≤
      2 * Real.sqrt p.1 * localGreen p (1 / 2) x y := by linarith only [h, hsource]
  calc
    _ ≤ (2 * Real.sqrt p.1 * localGreen p (1 / 2) x y) / ((p.1 : ℝ) + 1) :=
      div_le_div_of_nonneg_right hsum (degree_pos p).le
    _ = _ := by unfold spectralRatio; ring

private theorem harmonic_le_tempered (x y : LocalVertex p) :
    localGreen p 1 x y ≤
      (localGreen p 1 x x / localGreen p (1 / 2) x x) * localGreen p (1 / 2) x y := by
  have hR := localRatio_pos p x y
  have hR1 := localRatio_le_one p x y
  have hroot : localRatio p x y ≤ Real.sqrt (localRatio p x y) := by
    apply (Real.le_sqrt hR.le hR.le).mpr
    nlinarith only [mul_nonneg hR.le (sub_nonneg.mpr hR1)]
  have hA := localGreen_pos p (s := 1) zero_lt_one x x
  have hB := localGreen_pos p (s := 1 / 2) (by norm_num) x x
  rw [localGreen_self] at hA hB
  rw [localGreen, localGreen_self, localGreen_self, localGreen, Real.rpow_one,
    ← Real.sqrt_eq_rpow, ← mul_assoc, div_mul_cancel₀ _ hB.ne']
  exact mul_le_mul_of_nonneg_left hroot hA.le

/-- The tempered kernel contracts geometrically under uniform walk powers. -/
theorem tempered_iter_bound (x y : LocalVertex p) (N : ℕ) :
    ((walkStep p) ^ N) (localGreen p (1 / 2) x) y ≤
      spectralRatio p ^ N * localGreen p (1 / 2) x y := by
  induction N generalizing y with
  | zero => simp only [pow_zero, Module.End.one_apply, one_mul, le_refl]
  | succ N ih =>
      rw [pow_succ', Module.End.mul_apply]
      calc
        _ ≤ walkStep p ((spectralRatio p ^ N) • localGreen p (1 / 2) x) y :=
          walkStep_mono p (fun z => ih z) y
        _ = spectralRatio p ^ N * walkStep p (localGreen p (1 / 2) x) y := by
          rw [map_smul, Pi.smul_apply, smul_eq_mul]
        _ ≤ spectralRatio p ^ N * (spectralRatio p * localGreen p (1 / 2) x y) :=
          mul_le_mul_of_nonneg_left (tempered_step_le p x y)
            (pow_nonneg (spectralRatio_nonneg p) N)
        _ = _ := by rw [pow_succ]; ring

/-- The harmonic walk remainder decays geometrically against the tempered profile. -/
theorem harmonic_iter_bound (x y : LocalVertex p) (N : ℕ) :
    ((walkStep p) ^ N) (localGreen p 1 x) y ≤
      spectralRatio p ^ N *
        ((localGreen p 1 x x / localGreen p (1 / 2) x x) * localGreen p (1 / 2) x y) := by
  have hc : 0 ≤ localGreen p 1 x x / localGreen p (1 / 2) x x :=
    div_nonneg (localGreen_pos p zero_lt_one x x).le
      (localGreen_pos p (by norm_num : (0 : ℝ) < 1 / 2) x x).le
  calc
    _ ≤ ((walkStep p) ^ N)
        ((localGreen p 1 x x / localGreen p (1 / 2) x x) • localGreen p (1 / 2) x) y :=
      walkIter_mono p N (fun z => harmonic_le_tempered p x z) y
    _ = (localGreen p 1 x x / localGreen p (1 / 2) x x) *
        ((walkStep p) ^ N) (localGreen p (1 / 2) x) y := by
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
    _ ≤ (localGreen p 1 x x / localGreen p (1 / 2) x x) *
        (spectralRatio p ^ N * localGreen p (1 / 2) x y) :=
      mul_le_mul_of_nonneg_left (tempered_iter_bound p x y N) hc
    _ = _ := by ring

private def pointSource (x : LocalVertex p) : LocalVertex p → ℝ :=
  (((p.1 : ℝ) + 1)⁻¹) • pointMass p x

private theorem iter_pointSource (x y : LocalVertex p) (N : ℕ) :
    ((walkStep p) ^ N) (pointSource p x) y = walkMass p N x y / ((p.1 : ℝ) + 1) := by
  rw [pointSource, map_smul, Pi.smul_apply, smul_eq_mul]
  unfold walkMass
  ring

private theorem green_step_source (x : LocalVertex p) :
    localGreen p 1 x - walkStep p (localGreen p 1 x) = pointSource p x := by
  funext y
  have h := congrArg (fun t : ℝ => t / ((p.1 : ℝ) + 1)) (harmonic_source p x y)
  rw [sub_div, mul_div_cancel_left₀ _ (degree_pos p).ne'] at h
  change localGreen p 1 x y - (∑ w ∈ neighbors p y, localGreen p 1 x w) /
    ((p.1 : ℝ) + 1) = ((p.1 : ℝ) + 1)⁻¹ * pointMass p x y
  rw [h]
  ring

private theorem walk_telescope (f : LocalVertex p → ℝ) (N : ℕ) (y : LocalVertex p) :
    (∑ k ∈ Finset.range N, ((walkStep p) ^ k) (f - walkStep p f) y) =
      f y - ((walkStep p) ^ N) f y := by
  have hterm (k : ℕ) : ((walkStep p) ^ k) (f - walkStep p f) y =
      ((walkStep p) ^ k) f y - ((walkStep p) ^ (k + 1)) f y := by
    rw [map_sub, Pi.sub_apply, pow_succ, Module.End.mul_apply]
  simp_rw [hterm]
  rw [Finset.sum_range_sub']
  simp only [pow_zero, Module.End.one_apply]

/-- Finite occupation kernel, constructed solely from the actual walk. -/
def greenPartial (x : LocalVertex p) (N : ℕ) (y : LocalVertex p) : ℝ :=
  ∑ k ∈ Finset.range N, walkMass p k x y / ((p.1 : ℝ) + 1)

theorem greenPartial_eq (x y : LocalVertex p) (N : ℕ) :
    greenPartial p x N y = localGreen p 1 x y - ((walkStep p) ^ N) (localGreen p 1 x) y := by
  have h := walk_telescope p (localGreen p 1 x) N y
  rw [green_step_source] at h
  simpa only [iter_pointSource, greenPartial] using h

theorem tendsto_greenPartial (x y : LocalVertex p) :
    Tendsto (fun N => greenPartial p x N y) atTop (𝓝 (localGreen p 1 x y)) := by
  have hr : |spectralRatio p| < 1 := by
    rw [abs_of_nonneg (spectralRatio_nonneg p)]
    exact spectralRatio_lt_one p
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have hz : Tendsto (fun N => ((walkStep p) ^ N) (localGreen p 1 x) y) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun N => walkIter_nonneg p N (fun z => (localGreen_pos p zero_lt_one x z).le) y)
      (fun N => harmonic_iter_bound p x y N)
    simpa only [zero_mul] using hpow.mul_const
      ((localGreen p 1 x x / localGreen p (1 / 2) x x) * localGreen p (1 / 2) x y)
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => localGreen p 1 x y)
    atTop (𝓝 (localGreen p 1 x y))).sub hz
  simpa only [greenPartial_eq, sub_zero] using ht

/-- The intrinsic harmonic kernel is the actual convergent walk Green sum. -/
theorem hasSum_walkGreen (x y : LocalVertex p) :
    HasSum (fun N => walkMass p N x y / ((p.1 : ℝ) + 1)) (localGreen p 1 x y) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun N => div_nonneg (walkMass_nonneg p N x y) (degree_pos p).le) _).mpr
  exact tendsto_greenPartial p x y

private theorem greenPartial_le_supersolution (x : LocalVertex p) (u : LocalVertex p → ℝ)
    (hu : ∀ y, 0 ≤ u y)
    (hsource : ∀ y, pointMass p x y ≤ ((p.1 : ℝ) + 1) * u y -
      ∑ w ∈ neighbors p y, u w) (N : ℕ) (y : LocalVertex p) : greenPartial p x N y ≤ u y := by
  have hdiff : pointSource p x ≤ u - walkStep p u := by
    intro z
    have h := div_le_div_of_nonneg_right (hsource z) (degree_pos p).le
    rw [sub_div, mul_div_cancel_left₀ _ (degree_pos p).ne'] at h
    change ((p.1 : ℝ) + 1)⁻¹ * pointMass p x z ≤
      u z - (∑ w ∈ neighbors p z, u w) / ((p.1 : ℝ) + 1)
    simpa only [div_eq_mul_inv, mul_comm] using h
  calc
    _ = ∑ k ∈ Finset.range N, ((walkStep p) ^ k) (pointSource p x) y := by
      simp only [iter_pointSource, greenPartial]
    _ ≤ ∑ k ∈ Finset.range N, ((walkStep p) ^ k) (u - walkStep p u) y :=
      Finset.sum_le_sum fun k _ => walkIter_mono p k hdiff y
    _ = u y - ((walkStep p) ^ N) u y := walk_telescope p u N y
    _ ≤ u y := sub_le_self _ (walkIter_nonneg p N hu y)

/-- The walk kernel is the least nonnegative supersolution of the unit-source equation. -/
theorem localGreen_isLeast (x : LocalVertex p) :
    IsLeast {u : LocalVertex p → ℝ | (∀ y, 0 ≤ u y) ∧
      ∀ y, pointMass p x y ≤ ((p.1 : ℝ) + 1) * u y - ∑ w ∈ neighbors p y, u w}
      (localGreen p 1 x) := by
  constructor
  · exact ⟨fun y => (localGreen_pos p zero_lt_one x y).le,
      fun y => (harmonic_source p x y).symm.le⟩
  · intro u hu y
    exact le_of_tendsto (tendsto_greenPartial p x y)
      (Eventually.of_forall fun N => greenPartial_le_supersolution p x u hu.1 hu.2 N y)

/-- The harmonic diagonal excess is precisely the sum of return probabilities after time zero. -/
theorem hasSum_returns (x : LocalVertex p) :
    HasSum (fun N => walkMass p (N + 1) x x) (1 / ((p.1 : ℝ) - 1)) := by
  have htotal : HasSum (fun N => walkMass p N x x)
      (((p.1 : ℝ) + 1) * localGreen p 1 x x) := by
    have h := (hasSum_walkGreen p x x).mul_left ((p.1 : ℝ) + 1)
    simpa only [← mul_div_assoc, mul_div_cancel_left₀ _ (degree_pos p).ne'] using! h
  apply (hasSum_nat_add_iff (f := fun N => walkMass p N x x)
    (g := 1 / ((p.1 : ℝ) - 1)) 1).mpr
  have hp : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have hm : (p.1 : ℝ) - 1 ≠ 0 := by linarith only [hp]
  have hs : (p.1 : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith only [hp]
  have hvalue : 1 / ((p.1 : ℝ) - 1) +
      ∑ i ∈ Finset.range 1, walkMass p i x x = ((p.1 : ℝ) + 1) * localGreen p 1 x x := by
    simp only [Finset.sum_range_one, walkMass, pow_zero, Module.End.one_apply,
      pointMass, if_true, localGreen_self, treeGreen, Real.rpow_one, mul_one,
      Real.rpow_two]
    field_simp [hm, hs]
    ring
  rwa [hvalue]

#print axioms harmonic_iter_bound
#print axioms hasSum_walkGreen
#print axioms localGreen_isLeast
#print axioms hasSum_returns

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeWalk
