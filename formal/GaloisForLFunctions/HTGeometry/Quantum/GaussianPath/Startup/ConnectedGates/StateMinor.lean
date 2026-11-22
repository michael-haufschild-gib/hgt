import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw
import GaloisForLFunctions.HTGeometry.KrylovProjectedCompleteIncidenceLaw
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid

/-! # A two-spin amplitude minor detects entanglement at the identity -/
open Filter Matrix NormedSpace Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ConnectedGates
noncomputable section
variable {N : ℕ}
abbrev Bits (N : ℕ) := Fin N → Bool
abbrev Register (N : ℕ) := Matrix (Bits N) (Bits N) ℂ

/-- Configurations with only the two specified bits variable. -/
def corner (i j : Fin N) (p q : Bool) : Bits N :=
  fun k => if k=i then p else if k=j then q else false

/-- A two-by-two minor of the state obtained from the all-zero input. -/
def amplitudeMinor (i j : Fin N) (U : Register N) : ℂ :=
  let f (p q : Bool) := U (corner i j p q) (fun _ => false)
  f false false*f true true-f true false*f false true

private theorem corner_base (i j : Fin N) : corner i j false false=(fun _ => false) := by
  funext k; simp [corner]

local instance (n : ℕ) : CStarAlgebra (Register n) where

/-- The minor equals the two-spin transition amplitude of the generator
to first order, with a uniform quadratic remainder at every signed time. -/
theorem minor_linear_error (i j : Fin N) (hij : i≠j) (H : Register N) (hH : IsSelfAdjoint H) (t : ℝ) :
    ‖amplitudeMinor i j (unitaryEvolution H t)-
      ((t:ℂ)*(-Complex.I))*H (corner i j true true) (fun _ => false)‖ ≤ 5/2*(|t| * ‖H‖)^2 := by
  let r : Bits N := fun _ => false
  let U := unitaryEvolution H t
  let f (p q : Bool) := U (corner i j p q) r
  let a := (t:ℂ)*(-Complex.I)
  let M := |t| * ‖H‖
  have h0 : unitaryEvolution H 0=1 := by simp [unitaryEvolution]
  have hnear : ‖U-1‖≤M := by
    simpa only [U,h0,sub_zero,M,mul_comm] using norm_unitaryEvolution_time_sub_le hH t 0
  have hone : ‖f false false-1‖ ≤ M := by
    have h := (norm_entry_le_l2_opNorm (U-1) r r).trans hnear
    simpa only [f,corner_base,Matrix.sub_apply,Matrix.one_apply_eq,r] using h
  have hi (q : Bool) : corner i j true q≠r := by
    intro he; have hh := congrFun he i; simp [corner,r] at hh
  have hj : corner i j false true≠r := by
    intro he; have hh := congrFun he j; simp [corner,r,hij.symm] at hh
  have hoff (p q : Bool) (hne : corner i j p q ≠ r) : ‖f p q‖ ≤ M := by
    have h := (norm_entry_le_l2_opNorm (U-1) (corner i j p q) r).trans hnear
    simpa only [Matrix.sub_apply,Matrix.one_apply_ne hne,sub_zero] using h
  have hTaylor : selfAdjointHamiltonianTaylor H 1 t=1+a • H := by
    simp only [selfAdjointHamiltonianTaylor,cstarExponentialTaylor,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,one_smul,zero_add,a]
    rw [←Complex.real_smul,smul_assoc]
  have hmat : ‖U-(1+a • H)‖ ≤ M^2/2 := by
    have hh := norm_selfAdjoint_exp_sub_hamiltonianTaylor_le H hH 1 t
    rw [hTaylor] at hh
    simpa only [U,unitaryEvolution,M,mul_pow,mul_comm,show (1:ℕ)+1=2 from rfl,Nat.factorial_two,Nat.cast_ofNat] using hh
  let g := a*H (corner i j true true) r
  have hlin : ‖f true true-g‖≤M^2/2 := by
    have h := (norm_entry_le_l2_opNorm (U-(1+a • H)) (corner i j true true) r).trans hmat
    simpa only [Matrix.sub_apply,Matrix.add_apply,Matrix.one_apply_ne (hi _),zero_add,
      Matrix.smul_apply,smul_eq_mul] using h
  have hpair (p q : ℂ) (h₁ : ‖p‖≤M) (h₂ : ‖q‖≤M) : ‖p*q‖≤M^2 := by
    rw [norm_mul,pow_two]
    exact mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)
  change ‖f false false*f true true-f true false*f false true-g‖≤5/2*M^2
  rw [show f false false*f true true-f true false*f false true-g=
    ((f false false-1)*f true true+(f true true-g))-f true false*f false true by ring]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  have h₁ := hpair _ _ hone (hoff true true (hi true))
  have h₂ := hpair _ _ (hoff true false (hi false)) (hoff false true hj)
  linarith only [h₁,h₂,hlin]

/-- A nonzero two-spin transition gives a linear minor lower bound on
a punctured neighborhood of the identity. -/
theorem eventual_minor_lower (i j : Fin N) (hij : i≠j) (H : Register N) (hH : IsSelfAdjoint H)
    (hne : H (corner i j true true) (fun _ => false)≠0) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖H (corner i j true true) (fun _ => false)‖/2 * |t| <
      ‖amplitudeMinor i j (unitaryEvolution H t)‖ := by
  let z := H (corner i j true true) (fun _ => false)
  let L := 5/2*‖H‖^2
  have hL : 0≤L := by dsimp only [L]; positivity
  have hz : 0<‖z‖ := norm_pos_iff.mpr hne
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] 0, L * |t| < ‖z‖/2 := by
    have hc : Continuous (fun t : ℝ => L * |t|) := continuous_const.mul continuous_abs
    exact (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually_lt_const (by simpa using half_pos hz)
  filter_upwards [hsmall,self_mem_nhdsWithin] with t ht ht₀
  have hp : 0 < |t| := abs_pos.mpr (show t≠0 from ht₀)
  have he := minor_linear_error i j hij H hH t
  let f := amplitudeMinor i j (unitaryEvolution H t)
  have hnorm : ‖((t:ℂ)*(-Complex.I))*z‖ ≤ ‖f‖+‖f-((t:ℂ)*(-Complex.I))*z‖ := by
    calc _ = ‖f-(f-((t:ℂ)*(-Complex.I))*z)‖ := by congr 1; abel
         _ ≤ _ := norm_sub_le _ _
  have hn : ‖((t:ℂ)*(-Complex.I))*z‖=|t| * ‖z‖ := by
    rw [norm_mul,norm_mul,norm_neg,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hdiff : ‖f-((t:ℂ)*(-Complex.I))*z‖ ≤ (L * |t|) * |t| := he.trans_eq (by dsimp only [L]; ring)
  rw [hn] at hnorm
  change ‖z‖/2 * |t| < ‖f‖
  linarith only [hnorm,hdiff,mul_lt_mul_of_pos_right ht hp]

private theorem prod_error {a b c d : ℂ} (ha : ‖a‖≤1) (hd : ‖d‖≤1) :
    ‖a*b-c*d‖ ≤ ‖a-c‖+‖b-d‖ := by
  rw [show a*b-c*d=(a-c)*d+a*(b-d) by ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_mul]
  exact add_le_add (mul_le_of_le_one_right (norm_nonneg _) hd) (mul_le_of_le_one_left (norm_nonneg _) ha)

/-- Only errors in the all-zero input column enter the minor bound. -/
theorem minor_column_error (i j : Fin N) (U V : Register N) (hU : ‖U‖≤1) (hV : ‖V‖≤1)
    (δ : ℝ) (hδ : ∀ x, ‖(U-V) x (fun _ => false)‖ ≤ δ) :
    ‖amplitudeMinor i j U-amplitudeMinor i j V‖ ≤ 4*δ := by
  let r : Bits N := fun _ => false
  let f (A : Register N) (p q : Bool) := A (corner i j p q) r
  have h (p q a b : Bool) : ‖f U p q*f U a b-f V p q*f V a b‖≤2*δ := by
    apply (prod_error ((norm_entry_le_l2_opNorm U _ _).trans hU)
      ((norm_entry_le_l2_opNorm V _ _).trans hV)).trans
    rw [two_mul]
    exact add_le_add (hδ _) (hδ _)
  let A (X : Register N) := f X false false*f X true true
  let B (X : Register N) := f X true false*f X false true
  change ‖(A U-B U)-(A V-B V)‖≤_
  rw [show (A U-B U)-(A V-B V)=(A U-A V)-(B U-B V) by abel]
  exact (norm_sub_le ..).trans ((add_le_add (h false false true true) (h true false false true)).trans_eq (by ring))

#print axioms minor_linear_error
#print axioms minor_column_error
end
end GaloisForLFunctions.HTGeometry.ConnectedGates
