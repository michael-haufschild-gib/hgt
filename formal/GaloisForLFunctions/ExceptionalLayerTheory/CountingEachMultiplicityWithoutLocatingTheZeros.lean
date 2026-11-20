import GaloisForLFunctions.ExceptionalLayerTheory.TheHighDerivativeAreasOfAWholeObservationDisk
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev

/-!
# A finite census of zero multiplicities from whole-disk areas

Let W be the winding number and D the least common multiple of 1,…,W.
For i=1,…,W use derivative
order D/i−1. Its area law gives the ith ordinary moment of the numbers
m^(2/D), where m ranges over zero orders. The known candidate values
are 1,…,W. Lagrange interpolation on these values and zero gives an
explicit linear combination of areas for every multiplicity count.
No zero positions or number of distinct zeros enter the readout.
-/

noncomputable section
open Complex Filter Metric Polynomial Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

private def node (W n : ℕ) : ℝ := (n:ℝ)^(2/(Nat.lcmUpto W:ℝ))
private def levelOrder (W i : ℕ) := Nat.lcmUpto W/i-1
private def selector (W k : ℕ) : ℝ[X] := Lagrange.basis (Finset.range (W+1)) (node W) k

/-- Linear combination of derivative areas selected by the winding W
and the multiplicity k to be counted. -/
def diskMultiplicityReading (W k : ℕ) (c : ℂ) (R u : ℝ) :=
  ∑ i ∈ Finset.range (W+1), (selector W k).coeff i*xiDerivativeDiskArea (levelOrder W i) c R u

private theorem node_inj (W : ℕ) : Function.Injective (node W) := by
  apply StrictMono.injective
  intro a b hab
  exact Real.rpow_lt_rpow (Nat.cast_nonneg _) (by exact_mod_cast hab)
    (div_pos (by norm_num) (Nat.cast_pos.mpr (Nat.lcmUpto_pos W)))

private theorem powers_at_levels (W n : ℕ) {i : ℕ} (hi : 0 < i) (hiW : i ≤ W) :
    (n:ℝ)^(2/((levelOrder W i+1:ℕ):ℝ))=(node W n)^i := by
  have hd : i ∣ Nat.lcmUpto W := Finset.dvd_lcm (s:=Finset.Icc 1 W) (f:=id) (Finset.mem_Icc.mpr ⟨hi,hiW⟩)
  have he := Nat.div_mul_cancel hd
  have hq : 0 < Nat.lcmUpto W/i := by
    by_contra! hn
    have h₀ := Nat.eq_zero_of_le_zero hn
    rw [h₀,zero_mul] at he
    exact (Nat.lcmUpto_pos W).ne' he.symm
  have hlevel : levelOrder W i+1=Nat.lcmUpto W/i := by
    unfold levelOrder
    omega
  have he' : ((Nat.lcmUpto W/i:ℕ):ℝ)*(i:ℝ)=(Nat.lcmUpto W:ℝ) := by exact_mod_cast he
  rw [hlevel,node,←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  rw [←he']
  field_simp [Nat.cast_ne_zero.mpr hq.ne',Nat.cast_ne_zero.mpr hi.ne']

private theorem select_multiplicity {W k : ℕ} (hk : 0<k) (hkW : k≤W)
    {n : ℕ} (hn : n≤W) :
    (∑ i ∈ Finset.range (W+1), (selector W k).coeff i*(n:ℝ)^(2/((levelOrder W i+1:ℕ):ℝ))) =
      if n=k then 1 else 0 := by
  let P := selector W k
  have hkin : k∈Finset.range (W+1) := Finset.mem_range.mpr (by omega)
  have hp : 0<(2:ℝ)/(Nat.lcmUpto W:ℝ) := div_pos (by norm_num) (Nat.cast_pos.mpr (Nat.lcmUpto_pos W))
  have hzero : P.coeff 0=0 := by
    have h := Lagrange.eval_basis_of_ne (v:=node W) hk.ne' (Finset.mem_range.mpr (by omega : 0<W+1))
    simpa only [P,selector,node,Nat.cast_zero,Real.zero_rpow hp.ne',Polynomial.coeff_zero_eq_eval_zero] using h
  have hd : P.natDegree<W+1 := by
    change (Lagrange.basis _ _ _).natDegree<_
    rw [Lagrange.natDegree_basis (node_inj W).injOn hkin,Finset.card_range]
    omega
  calc _ = ∑ i ∈ Finset.range (W+1), P.coeff i*(node W n)^i := by
             apply Finset.sum_congr rfl
             intro i hi
             by_cases h : i=0
             · subst i; change P.coeff 0*_ = _; rw [hzero,zero_mul,zero_mul]
             · rw [powers_at_levels W n (Nat.pos_of_ne_zero h) (by simpa using Finset.mem_range.mp hi)]
       _ = P.eval (node W n) := (Polynomial.eval_eq_sum_range' hd _).symm
       _ = _ := by
             by_cases he : n=k
             · subst n
               exact (Lagrange.eval_basis_self (node_inj W).injOn hkin).trans (if_pos rfl).symm
             · rw [if_neg he]
               exact Lagrange.eval_basis_of_ne (Ne.symm he) (Finset.mem_range.mpr (by omega))

/-- The winding of the circle specifies a finite family of whole-disk
readings whose limits are the complete histogram of the interior divisor. -/
theorem whole_disk_multiplicity_histogram (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
    ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
      (∀ z ∈ t, hadamardOrder z≤W) ∧ ∀ k : ℕ, 0<k → k≤W →
        Tendsto (diskMultiplicityReading W k c R) atTop
          (𝓝 ((t.filter (fun z => hadamardOrder z=k)).card:ℝ)) := by
  classical
  obtain ⟨t,ht,hw,harea⟩ := xi_disk_fractional_moments c hR hb
  let W := ∑ z ∈ t, hadamardOrder z
  have hW : (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat=W := by
    rw [hw,←Nat.cast_sum,Int.toNat_natCast]
  dsimp only
  rw [hW]
  have hcap (z : ℂ) (hz : z∈t) : hadamardOrder z≤W :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hz
  refine ⟨t,ht,hcap,?_⟩
  intro k hk hkW
  have hlim := tendsto_finsetSum (Finset.range (W+1)) fun i _ =>
    (harea (levelOrder W i)).const_mul ((selector W k).coeff i)
  have he : (∑ i ∈ Finset.range (W+1), (selector W k).coeff i*
      ∑ z ∈ t, (hadamardOrder z:ℝ)^(2/((levelOrder W i+1:ℕ):ℝ))) =
      ((t.filter (fun z => hadamardOrder z=k)).card:ℝ) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc _ = ∑ z ∈ t, if hadamardOrder z=k then (1:ℝ) else 0 :=
                 Finset.sum_congr rfl fun z hz => select_multiplicity hk hkW (hcap z hz)
         _ = _ := by rw [←Finset.sum_filter]; simp
  rwa [he] at hlim

#print axioms whole_disk_multiplicity_histogram
end GaloisForLFunctions.ExceptionalLayerTheory
