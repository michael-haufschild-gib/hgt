import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryCoefficients
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicGradedCoefficient
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polynomial surgery on a planar radial domain

The surgery domain is a compact, radial, nonconvex set with nonempty interior.
Six explicit polynomial inequalities define it. A homothetic copy of the
original wedge lies inside it, while all lower-degree extremal grids survive
and the distinguished higher-degree node is removed.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set


def recoveryPlaneEval (P : Polynomial (Polynomial ℝ)) (p : ℝ × ℝ) : ℝ :=
  Polynomial.eval₂ (Polynomial.evalRingHom p.1) p.2 P

theorem recoveryPlaneEval_continuous (P : Polynomial (Polynomial ℝ)) :
    Continuous (recoveryPlaneEval P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    change Continuous (fun p : ℝ × ℝ =>
      Polynomial.eval₂ (Polynomial.evalRingHom p.1) p.2 (P+Q))
    simp only [Polynomial.eval₂_add]
    exact hP.add hQ
  | monomial n P =>
    change Continuous (fun p : ℝ × ℝ =>
      Polynomial.eval₂ (Polynomial.evalRingHom p.1) p.2 (Polynomial.monomial n P))
    simp only [Polynomial.eval₂_monomial]
    exact (P.continuous.comp continuous_fst).mul (continuous_snd.pow n)

def recoveryHomogeneousProfile (k : ℕ) (P : cubicHomogeneousSpace k) : ℝ[X] :=
  cubicDehomogeneousPolynomial k (cubicHomogeneousCoordinates k P)

def recoveryHomogeneousLift (k : ℕ) (R : ℝ[X]) : cubicHomogeneousSpace k :=
  (cubicHomogeneousCoordinatesEquiv k).symm (fun i => R.coeff i.val)

theorem recoveryHomogeneousProfile_degree (k : ℕ) (P : cubicHomogeneousSpace k) :
    (recoveryHomogeneousProfile k P).natDegree ≤ k :=
  cubicDehomogeneousPolynomial_degree k _

theorem recoveryHomogeneousProfile_coefficient (k : ℕ) (P : cubicHomogeneousSpace k)
    (i : Fin (k+1)) :
    (recoveryHomogeneousProfile k P).coeff i.val = cubicHomogeneousCoordinates k P i :=
  cubicDehomogeneousPolynomial_coefficient k _ i

theorem recoveryHomogeneousProfile_lift (k : ℕ) (R : ℝ[X]) (hR : R.natDegree ≤ k) :
    recoveryHomogeneousProfile k (recoveryHomogeneousLift k R) = R := by
  ext i
  by_cases hi : i < k+1
  · rw [recoveryHomogeneousProfile_coefficient k _ ⟨i,hi⟩]
    change ((cubicHomogeneousCoordinatesEquiv k)
      ((cubicHomogeneousCoordinatesEquiv k).symm (fun j => R.coeff j.val))) ⟨i,hi⟩ = _
    rw [LinearEquiv.apply_symm_apply]
  · rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · omega
    · have := recoveryHomogeneousProfile_degree k (recoveryHomogeneousLift k R)
      omega

theorem recoveryHomogeneousLift_profile (k : ℕ) (P : cubicHomogeneousSpace k) :
    recoveryHomogeneousLift k (recoveryHomogeneousProfile k P) = P := by
  apply (cubicHomogeneousCoordinatesEquiv k).injective
  rw [recoveryHomogeneousLift, LinearEquiv.apply_symm_apply]
  funext i
  exact recoveryHomogeneousProfile_coefficient k P i

theorem recoveryHomogeneousProfile_missing (k : ℕ) (P : cubicHomogeneousSpace (k+1)) :
    (recoveryHomogeneousProfile (k+1) P).coeff k = cubicGradedCoefficient k P :=
  recoveryHomogeneousProfile_coefficient (k+1) P (cubicMissingIndex k)

theorem recoveryPlaneEval_radial (k : ℕ) (P : cubicHomogeneousSpace k) (r c : ℝ) :
    recoveryPlaneEval P.val (c*r,c) = c^k*(recoveryHomogeneousProfile k P).eval r := by
  rw [← cubicHomogeneousCoordinates_reconstruct k P]
  unfold recoveryPlaneEval cubicHomogeneousPolynomial recoveryHomogeneousProfile
  rw [eval₂_finsetSum, cubicDehomogeneousPolynomial_evaluation, Finset.mul_sum]
  simp only [eval₂_monomial, coe_evalRingHom, eval_monomial, mul_pow]
  apply Finset.sum_congr rfl
  intro i _
  have he : i.val+(k-i.val) = k := by omega
  calc
    _ = (c^i.val*c^(k-i.val))*(cubicHomogeneousCoordinates k P i*r^i.val) := by ring
    _ = _ := by rw [← pow_add, he]

theorem recoveryPlaneEval_top (k : ℕ) (P : cubicHomogeneousSpace k) (r : ℝ) :
    recoveryPlaneEval P.val (r,1) = (recoveryHomogeneousProfile k P).eval r := by
  simpa only [one_mul, one_pow] using recoveryPlaneEval_radial k P r 1

theorem recoveryPlaneEval_scale (k : ℕ) (P : cubicHomogeneousSpace k) (q : ℝ) (p : ℝ × ℝ) :
    recoveryPlaneEval P.val (q*p.1,q*p.2) = q^k*recoveryPlaneEval P.val p := by
  rw [← cubicHomogeneousCoordinates_reconstruct k P]
  simp only [recoveryPlaneEval, cubicHomogeneousPolynomial, eval₂_finsetSum,
    eval₂_monomial, coe_evalRingHom, eval_monomial, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : i.val+(k-i.val)=k := by omega
  calc
    _ = (q^i.val*q^(k-i.val))*
      (cubicHomogeneousCoordinates k P i*p.1^i.val*p.2^(k-i.val)) := by ring
    _ = _ := by rw [← pow_add, he]

def recoveryWedge : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 3*p.2}

theorem recoveryWedge_param (r c : ℝ) (hr : r ∈ Icc (1 : ℝ) 3) (hc : c ∈ Icc (0 : ℝ) 1) :
    (c*r,c) ∈ recoveryWedge := by
  refine ⟨hc.1,hc.2,?_,?_⟩
  · nlinarith [mul_nonneg hc.1 (sub_nonneg.mpr hr.1)]
  · nlinarith [mul_nonneg hc.1 (sub_nonneg.mpr hr.2)]

theorem recoveryWedge_representation (p : ℝ × ℝ) (hp : p ∈ recoveryWedge) :
    ∃ r ∈ Icc (1 : ℝ) 3, ∃ c ∈ Icc (0 : ℝ) 1, p = (c*r,c) := by
  by_cases hc : p.2=0
  · refine ⟨1,⟨le_rfl,by linarith⟩,0,⟨le_rfl,zero_le_one⟩,?_⟩
    have hu : p.1=0 := by rcases hp with ⟨h0,h1,h2,h3⟩; rw [hc] at h2 h3; linarith
    exact Prod.ext (by simpa using hu) hc
  · have hc0 : 0 < p.2 := lt_of_le_of_ne hp.1 (Ne.symm hc)
    refine ⟨p.1/p.2,⟨(le_div_iff₀ hc0).mpr (by simpa using hp.2.2.1),
      (div_le_iff₀ hc0).mpr hp.2.2.2⟩,p.2,⟨hp.1,hp.2.1⟩,?_⟩
    apply Prod.ext
    · field_simp
    · rfl

theorem recoveryWedge_closed : IsClosed recoveryWedge := by
  exact (isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd continuous_const).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst (continuous_const.mul continuous_snd))))

theorem recoveryWedge_compact : IsCompact recoveryWedge := by
  apply (isCompact_Icc (a := ((0 : ℝ),(0 : ℝ))) (b := (3,1))).of_isClosed_subset recoveryWedge_closed
  intro p hp
  rcases hp with ⟨h0,h1,h2,h3⟩
  exact ⟨⟨by linarith,h0⟩,⟨by linarith,h1⟩⟩

def recoveryCutPolynomial (n : ℕ) : cubicHomogeneousSpace (n+2) :=
  recoveryHomogeneousLift (n+2) (taylor (-2 : ℝ) (recoverySurgeryPolynomial n))

def recoverySurgeryDomain (n : ℕ) : Set (ℝ × ℝ) :=
  recoveryWedge ∩ {p | |recoveryPlaneEval (recoveryCutPolynomial n).val p| ≤ recoverySurgeryHeight n}

theorem recoveryCutPolynomial_profile (n : ℕ) :
    recoveryHomogeneousProfile (n+2) (recoveryCutPolynomial n) =
      taylor (-2 : ℝ) (recoverySurgeryPolynomial n) := by
  apply recoveryHomogeneousProfile_lift
  rw [natDegree_taylor]
  exact recoverySurgeryPolynomial_degree n

theorem recoveryCutPolynomial_missing (n : ℕ) :
    cubicGradedCoefficient (n+1) (recoveryCutPolynomial n) =
      -(n+2 : ℝ)*(2 : ℝ)^(n+2) := by
  rw [← recoveryHomogeneousProfile_missing, recoveryCutPolynomial_profile,
    recoverySurgeryPolynomial_shifted_penultimate]

theorem recoveryCutPolynomial_radial (n : ℕ) (r c : ℝ) :
    recoveryPlaneEval (recoveryCutPolynomial n).val (c*r,c) =
      c^(n+2)*(recoverySurgeryPolynomial n).eval (r-2) := by
  rw [recoveryPlaneEval_radial, recoveryCutPolynomial_profile, taylor_eval]
  rfl

theorem recoverySurgeryDomain_closed (n : ℕ) : IsClosed (recoverySurgeryDomain n) :=
  recoveryWedge_closed.inter
    (isClosed_le (recoveryPlaneEval_continuous _).abs continuous_const)

theorem recoverySurgeryDomain_compact (n : ℕ) : IsCompact (recoverySurgeryDomain n) :=
  recoveryWedge_compact.of_isClosed_subset (recoverySurgeryDomain_closed n) inter_subset_left

theorem recoverySurgeryHeight_positive (n : ℕ) : 0 < recoverySurgeryHeight n := by
  unfold recoverySurgeryHeight
  linarith [recoverySurgeryEpsilon_lt_one n]

theorem recoverySurgeryHeight_lt_one (n : ℕ) : recoverySurgeryHeight n < 1 := by
  unfold recoverySurgeryHeight
  linarith [recoverySurgeryEpsilon_pos n]

def recoverySurgeryEnvelope (n : ℕ) : ℝ :=
  1+recoverySurgeryEpsilon n*(4*(n+2 : ℝ)+1)

def recoverySurgeryCorePower (n : ℕ) : ℝ :=
  recoverySurgeryHeight n/recoverySurgeryEnvelope n

def recoverySurgeryCoreScale (n : ℕ) : ℝ :=
  (recoverySurgeryCorePower n)^((n+2 : ℝ)⁻¹)

theorem recoverySurgeryEnvelope_gt_one (n : ℕ) : 1 < recoverySurgeryEnvelope n := by
  have hp : 0 < recoverySurgeryEpsilon n*(4*(n+2 : ℝ)+1) :=
    mul_pos (recoverySurgeryEpsilon_pos n) (by positivity)
  exact lt_add_of_pos_right 1 hp

theorem recoverySurgeryCorePower_positive (n : ℕ) : 0 < recoverySurgeryCorePower n :=
  div_pos (recoverySurgeryHeight_positive n) (lt_trans zero_lt_one (recoverySurgeryEnvelope_gt_one n))

theorem recoverySurgeryCorePower_lt_one (n : ℕ) : recoverySurgeryCorePower n < 1 := by
  apply (div_lt_one (lt_trans zero_lt_one (recoverySurgeryEnvelope_gt_one n))).mpr
  exact lt_trans (recoverySurgeryHeight_lt_one n) (recoverySurgeryEnvelope_gt_one n)

theorem recoverySurgeryCoreScale_positive (n : ℕ) : 0 < recoverySurgeryCoreScale n :=
  Real.rpow_pos_of_pos (recoverySurgeryCorePower_positive n) _

theorem recoverySurgeryCoreScale_lt_one (n : ℕ) : recoverySurgeryCoreScale n < 1 :=
  Real.rpow_lt_one (le_of_lt (recoverySurgeryCorePower_positive n))
    (recoverySurgeryCorePower_lt_one n) (by positivity)

theorem recoverySurgeryCoreScale_power (n : ℕ) :
    (recoverySurgeryCoreScale n)^(n+2) = recoverySurgeryCorePower n := by
  simpa only [recoverySurgeryCoreScale, Nat.cast_add, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (le_of_lt (recoverySurgeryCorePower_positive n))
      (show n+2 ≠ 0 by omega)

theorem recoverySurgeryCorePower_mul_envelope (n : ℕ) :
    recoverySurgeryCorePower n*recoverySurgeryEnvelope n = recoverySurgeryHeight n :=
  div_mul_cancel₀ _ (ne_of_gt (lt_trans zero_lt_one (recoverySurgeryEnvelope_gt_one n)))

theorem recoverySurgeryDomain_core_param (n : ℕ) (r c : ℝ)
    (hr : r ∈ Icc (1 : ℝ) 3) (hc : c ∈ Icc (0 : ℝ) (recoverySurgeryCoreScale n)) :
    (c*r,c) ∈ recoverySurgeryDomain n := by
  refine ⟨recoveryWedge_param r c hr ⟨hc.1,hc.2.trans (le_of_lt (recoverySurgeryCoreScale_lt_one n))⟩,?_⟩
  change |recoveryPlaneEval (recoveryCutPolynomial n).val (c*r,c)| ≤ _
  rw [recoveryCutPolynomial_radial, abs_mul, abs_of_nonneg (pow_nonneg hc.1 _)]
  have hp := pow_le_pow_left₀ hc.1 hc.2 (n+2)
  have hv : |(recoverySurgeryPolynomial n).eval (r-2)| ≤ recoverySurgeryEnvelope n :=
    recoverySurgeryPolynomial_bound n (r-2) (by rw [abs_le]; constructor <;> linarith [hr.1,hr.2])
  calc
    _ ≤ (recoverySurgeryCoreScale n)^(n+2)*recoverySurgeryEnvelope n :=
      mul_le_mul hp hv (abs_nonneg _) (pow_nonneg (le_of_lt (recoverySurgeryCoreScale_positive n)) _)
    _ = _ := by rw [recoverySurgeryCoreScale_power, recoverySurgeryCorePower_mul_envelope]

theorem recoverySurgeryDomain_core (n : ℕ) (p : ℝ × ℝ) (hp : p ∈ recoveryWedge) :
    (recoverySurgeryCoreScale n*p.1,recoverySurgeryCoreScale n*p.2) ∈ recoverySurgeryDomain n := by
  obtain ⟨r,hr,c,hc,rfl⟩ := recoveryWedge_representation p hp
  have he : recoverySurgeryCoreScale n*(c*r) = (recoverySurgeryCoreScale n*c)*r := by ring
  rw [he]
  apply recoverySurgeryDomain_core_param n r _ hr
  refine ⟨mul_nonneg (le_of_lt (recoverySurgeryCoreScale_positive n)) hc.1,?_⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc.2
    (le_of_lt (recoverySurgeryCoreScale_positive n))

theorem recoverySurgeryDomain_radial (n : ℕ) (p : ℝ × ℝ) (hp : p ∈ recoverySurgeryDomain n)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) : (q*p.1,q*p.2) ∈ recoverySurgeryDomain n := by
  refine ⟨?_,?_⟩
  · rcases recoveryWedge_representation p hp.1 with ⟨r,hr,c,hc,rfl⟩
    have he : q*(c*r) = (q*c)*r := by ring
    rw [he]
    apply recoveryWedge_param r _ hr
    exact ⟨mul_nonneg hq.1 hc.1,
      (mul_le_mul hq.2 hc.2 hc.1 zero_le_one).trans_eq (one_mul _)⟩
  · change |recoveryPlaneEval (recoveryCutPolynomial n).val (q*p.1,q*p.2)| ≤ _
    rw [recoveryPlaneEval_scale, abs_mul, abs_of_nonneg (pow_nonneg hq.1 _)]
    exact (mul_le_mul (pow_le_one₀ hq.1 hq.2) hp.2 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem recoverySurgeryDomain_interior (n : ℕ) : (interior (recoverySurgeryDomain n)).Nonempty := by
  let S : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < recoverySurgeryCoreScale n ∧
    p.2 < p.1 ∧ p.1 < 3*p.2}
  have hopen : IsOpen S :=
    (isOpen_lt continuous_const continuous_snd).inter
      ((isOpen_lt continuous_snd continuous_const).inter
        ((isOpen_lt continuous_snd continuous_fst).inter
          (isOpen_lt continuous_fst (continuous_const.mul continuous_snd))))
  have hsub : S ⊆ recoverySurgeryDomain n := by
    intro p hp
    have hw : p ∈ recoveryWedge := ⟨le_of_lt hp.1,
      (le_of_lt hp.2.1).trans (le_of_lt (recoverySurgeryCoreScale_lt_one n)),
      le_of_lt hp.2.2.1,le_of_lt hp.2.2.2⟩
    obtain ⟨r,hr,c,hc,he⟩ := recoveryWedge_representation p hw
    have hpc : p.2=c := congrArg Prod.snd he
    rw [he]
    exact recoverySurgeryDomain_core_param n r c hr ⟨hc.1,by rw [← hpc]; exact le_of_lt hp.2.1⟩
  have hx : (recoverySurgeryCoreScale n,recoverySurgeryCoreScale n/2) ∈ S := by
    have hq := recoverySurgeryCoreScale_positive n
    change 0 < recoverySurgeryCoreScale n/2 ∧ _
    constructor
    · positivity
    exact ⟨by linarith,by linarith,by linarith⟩
  exact ⟨_,mem_interior.mpr ⟨S,hsub,hopen,hx⟩⟩

theorem recoverySurgeryDomain_protected (n : ℕ) (l : Fin (n+1)) (i : Fin (l.val+2)) :
    (2+Chebyshev.node (l.val+1) i.val,1) ∈ recoverySurgeryDomain n := by
  have hx := Chebyshev.node_mem_Icc (n := l.val+1) (i := i.val)
  refine ⟨?_,?_⟩
  · exact ⟨zero_le_one,le_rfl,by linarith [hx.1],by linarith [hx.2]⟩
  · have he := recoveryCutPolynomial_radial n (2+Chebyshev.node (l.val+1) i.val) 1
    simp only [one_mul, one_pow] at he
    have hr : 2+Chebyshev.node (l.val+1) i.val-2 = Chebyshev.node (l.val+1) i.val := by ring
    rw [hr] at he
    change |recoveryPlaneEval (recoveryCutPolynomial n).val _| ≤ _
    rw [he]
    exact le_of_lt (recoverySurgery_lower_grid n l i)

theorem recoverySurgeryDomain_excluded (n : ℕ) :
    (2+Chebyshev.node (n+2) 1,1) ∉ recoverySurgeryDomain n := by
  intro hp
  have he := recoveryCutPolynomial_radial n (2+Chebyshev.node (n+2) 1) 1
  simp only [one_mul, one_pow] at he
  have hr : 2+Chebyshev.node (n+2) 1-2 = Chebyshev.node (n+2) 1 := by ring
  rw [hr] at he
  have hb := hp.2
  change |recoveryPlaneEval (recoveryCutPolynomial n).val _| ≤ _ at hb
  rw [he] at hb
  have hl := (abs_le.mp hb).1
  linarith [recoverySurgeryPolynomial_distinguished n, recoverySurgeryHeight_lt_one n]

theorem recoverySurgeryDomain_not_convex (n : ℕ) : ¬ Convex ℝ (recoverySurgeryDomain n) := by
  intro hK
  have h3 := recoverySurgeryDomain_protected n ⟨0,by omega⟩ ⟨0,by omega⟩
  change (2+Chebyshev.node 1 0,1) ∈ recoverySurgeryDomain n at h3
  rw [Chebyshev.node_eq_one, show (2 : ℝ)+1=3 by ring] at h3
  have h1 := recoverySurgeryDomain_protected n ⟨0,by omega⟩ ⟨1,by omega⟩
  change (2+Chebyshev.node 1 1,1) ∈ recoverySurgeryDomain n at h1
  rw [Chebyshev.node_eq_neg_one (show 1 ≠ (0 : ℕ) by omega),
    show (2 : ℝ)+(-1)=1 by ring] at h1
  have hx := Chebyshev.node_mem_Icc (n := n+2) (i := 1)
  have hc := hK h1 h3
    (show 0 ≤ (1-Chebyshev.node (n+2) 1)/2 by linarith [hx.2])
    (show 0 ≤ (1+Chebyshev.node (n+2) 1)/2 by linarith [hx.1])
    (show (1-Chebyshev.node (n+2) 1)/2+(1+Chebyshev.node (n+2) 1)/2=1 by ring)
  apply recoverySurgeryDomain_excluded n
  convert hc using 1
  ext <;> simp <;> ring

def recoverySurgeryConstraints (n : ℕ) : Fin 6 → Polynomial (Polynomial ℝ) :=
  ![X,1-X,C X-X,3*X-C X,
    C (C (recoverySurgeryHeight n))-(recoveryCutPolynomial n).val,
    C (C (recoverySurgeryHeight n))+(recoveryCutPolynomial n).val]

theorem recoverySurgeryDomain_polynomial_inequalities (n : ℕ) (p : ℝ × ℝ) :
    p ∈ recoverySurgeryDomain n ↔
      ∀ i : Fin 6, 0 ≤ recoveryPlaneEval (recoverySurgeryConstraints n i) p := by
  constructor
  · intro hp i
    rcases hp.1 with ⟨h0,h1,h2,h3⟩
    have hF := abs_le.mp (show |recoveryPlaneEval (recoveryCutPolynomial n).val p| ≤
      recoverySurgeryHeight n from hp.2)
    change -recoverySurgeryHeight n ≤
      eval₂ (evalRingHom p.1) p.2 (recoveryCutPolynomial n).val ∧
      eval₂ (evalRingHom p.1) p.2 (recoveryCutPolynomial n).val ≤ recoverySurgeryHeight n at hF
    fin_cases i <;> simp [recoverySurgeryConstraints,recoveryPlaneEval] <;> linarith [hF.1,hF.2]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    simp [recoverySurgeryConstraints,recoveryPlaneEval] at h0 h1 h2 h3 h4 h5
    refine ⟨⟨h0,by linarith,by linarith,by linarith⟩,?_⟩
    change |eval₂ (evalRingHom p.1) p.2 (recoveryCutPolynomial n).val| ≤ recoverySurgeryHeight n
    rw [abs_le]
    constructor <;> linarith

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
