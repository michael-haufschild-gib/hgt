import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspThreeAtomCauchyTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspPairRadialValues
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourNativeBulk

/-!
# The odd-four fibre through three atoms

The reflected pair of the first three theta atoms splits into the nine ordered atom pairs. The
diagonal pairs `(2,2)` and `(3,3)` are rescaled first atoms and contribute nonnegatively; each
unequal pair is an exact radial polynomial. With the Cauchy tail beyond three atoms, the native
odd fibre form is bounded below by `K(q)` times the explicit three-atom matrix
`R¹¹ + 8e^{-3q}R¹² + 18e^{-8q}R¹³ + 72e^{-11q}R²³`, `K(q) = 4q²e^{x-2q}`, minus the tail.
-/

open Real
namespace RHTower.ThetaCuspOddFourThreeAtom
noncomputable section
open ThetaCuspThreeAtomCauchyTail ThetaCuspOddCentral HTGeometry.SignedPoisson

/-- The `a`-th atom is the rescaled first atom at the shifted center. -/
theorem atom_shift {a : ℕ} (ha : 0 < a) (x : ℝ) :
    thetaCuspSourceTerm x a = (a:ℝ)^(-(1/2:ℝ))*thetaCuspSourceTerm (x+Real.log a) 1 := by
  have h := invSqrt_mul_thetaCuspSourceTerm_shift (q:=a) ha 1 x
  simpa only [Nat.mul_one] using h.symm

/-- Diagonal atom pairs are rescaled first-atom pairs. -/
theorem atomPair_diag_eq_shift {a : ℕ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    thetaCuspAtomPairReflectionJet n a a x =
      ((a:ℝ)^(-(1/2:ℝ)))^2*thetaCuspFirstAtomReflectionJet n (x+Real.log a) := by
  have hf : (fun t : ℝ => thetaCuspSourceTerm (x+t) a*thetaCuspSourceTerm (x-t) a) =
      fun t : ℝ => ((a:ℝ)^(-(1/2:ℝ)))^2*
        (thetaCuspSourceTerm ((x+Real.log a)+t) 1*thetaCuspSourceTerm ((x+Real.log a)-t) 1) := by
    funext t
    rw [atom_shift ha, atom_shift ha,
      show x+t+Real.log a=(x+Real.log a)+t by ring,
      show x-t+Real.log a=(x+Real.log a)-t by ring]
    ring
  unfold thetaCuspAtomPairReflectionJet thetaCuspFirstAtomReflectionJet
  rw [hf, iteratedDeriv_const_mul_field]

/-- Diagonal atom pairs have a nonnegative odd-four block once their shifted scale is at least
five. -/
theorem atomPair_diag_oddFour_nonneg {a : ℕ} (ha : 0 < a) {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 (x+Real.log a)) (c : Fin 4 → ℝ) :
    0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) a a x := by
  have hn := (firstAtomOddFour_posDef hq).posSemidef.dotProduct_mulVec_nonneg c
  have he : (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) a a x) =
      ((a:ℝ)^(-(1/2:ℝ)))^2*(star c ⬝ᵥ (firstAtomOddFour (x+Real.log a)).mulVec c) := by
    simp only [atomPair_diag_eq_shift ha, firstAtomOddFour,
      Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [he]
  exact mul_nonneg (sq_nonneg _) hn

/-- The scale of the `a`-th atom. -/
theorem scale_atom (a : ℕ) (x : ℝ) :
    thetaCuspSingleAtomReflectionScale a x = (a:ℝ)^2*thetaCuspSingleAtomReflectionScale 1 x := by
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
  ring

theorem scale_shift (a : ℕ) (ha : 0 < a) (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 (x+Real.log a) =
      (a:ℝ)^2*thetaCuspSingleAtomReflectionScale 1 x := by
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
  rw [show 2*(x+Real.log a) = 2*x+2*Real.log a by ring, Real.exp_add,
    show 2*Real.log (a:ℝ) = Real.log ((a:ℝ)^2) by rw [Real.log_pow]; norm_num,
    Real.exp_log (by positivity)]
  ring

/-- The signed even jet of an atom pair, from the radial recurrence. -/
theorem signed_pair_even (a b k : ℕ) (x : ℝ) :
    (-1:ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) a b x =
      4*((a:ℝ)^2*(b:ℝ)^2*thetaCuspSingleAtomReflectionScale 1 x^2)*
        Real.exp (x-((a:ℝ)^2+(b:ℝ)^2)*thetaCuspSingleAtomReflectionScale 1 x)*
        (thetaPairRadialEvenPolynomial ((a:ℝ)^2*(b:ℝ)^2*thetaCuspSingleAtomReflectionScale 1 x^2) k).eval
          (((a:ℝ)^2+(b:ℝ)^2)*thetaCuspSingleAtomReflectionScale 1 x) := by
  have h := thetaCuspAtomPairEvenJet_eq_radial a b k x
  change thetaCuspAtomPairReflectionJet (2*k) a b x = _ at h
  have hs : (-1:ℝ)^k*(-1:ℝ)^k = 1 := by rw [← mul_pow]; norm_num
  set qa := thetaCuspSingleAtomReflectionScale a x
  set qb := thetaCuspSingleAtomReflectionScale b x
  set q := thetaCuspSingleAtomReflectionScale 1 x
  have hqa : qa = (a:ℝ)^2*q := scale_atom a x
  have hqb : qb = (b:ℝ)^2*q := scale_atom b x
  have e1 : qa*qb = (a:ℝ)^2*(b:ℝ)^2*q^2 := by rw [hqa, hqb]; ring
  have e2 : x-qa-qb = x-((a:ℝ)^2+(b:ℝ)^2)*q := by rw [hqa, hqb]; ring
  have e3 : qa+qb = ((a:ℝ)^2+(b:ℝ)^2)*q := by rw [hqa, hqb]; ring
  calc (-1:ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) a b x
      = ((-1:ℝ)^k*(-1:ℝ)^k)*(4*(qa*qb)*Real.exp (x-qa-qb)*
          (thetaPairRadialEvenPolynomial (qa*qb) k).eval (qa+qb)) := by rw [h]; ring
    _ = _ := by rw [hs, one_mul, e1, e2, e3]


/-- The three-atom source as a sum over the first three atoms. -/
theorem threeAtomSource_eq_sum (y : ℝ) :
    thetaCuspThreeAtomSource y = ∑ a ∈ Finset.range 3, thetaCuspSourceTerm y (a+1) := by
  simp [thetaCuspThreeAtomSource, Finset.sum_range_succ]

/-- The three-atom reflected jet is the sum of the nine ordered atom-pair jets. -/
theorem threeAtomJet_eq_sum (n : ℕ) (x : ℝ) :
    thetaCuspThreeAtomReflectionJet n x =
      ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3,
        thetaCuspAtomPairReflectionJet n (a+1) (b+1) x := by
  have hf : (fun t => thetaCuspThreeAtomSource (x+t)*thetaCuspThreeAtomSource (x-t)) =
      fun t => ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3,
        thetaCuspSourceTerm (x+t) (a+1)*thetaCuspSourceTerm (x-t) (b+1) := by
    funext t
    rw [threeAtomSource_eq_sum, threeAtomSource_eq_sum, Finset.sum_mul_sum]
  have hsm (a b : ℕ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun t => thetaCuspSourceTerm (x+t) (a+1)*thetaCuspSourceTerm (x-t) (b+1)) :=
    ((contDiff_thetaCuspSourceAtom (a+1)).comp (contDiff_const.add contDiff_id)).mul
      ((contDiff_thetaCuspSourceAtom (b+1)).comp (contDiff_const.sub contDiff_id))
  unfold thetaCuspThreeAtomReflectionJet
  rw [hf, iteratedDeriv_fun_sum (fun a _ => (ContDiff.sum fun b _ => hsm a b).contDiffAt.of_le
    (by exact_mod_cast le_top))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [iteratedDeriv_fun_sum (fun b _ => (hsm a b).contDiffAt.of_le (by exact_mod_cast le_top))]
  rfl

/-- The exact three-atom odd matrix entry of order `m`, in units of `K(q) = 4q²e^{x-2q}`. -/
def threeAtomOddEntry (q : ℝ) (m : ℕ) : ℝ :=
  (thetaPairRadialEvenPolynomial (1*q^2) m).eval (2*q) +
    8*Real.exp (-3*q)*(thetaPairRadialEvenPolynomial (4*q^2) m).eval (5*q) +
    18*Real.exp (-8*q)*(thetaPairRadialEvenPolynomial (9*q^2) m).eval (10*q) +
    72*Real.exp (-11*q)*(thetaPairRadialEvenPolynomial (36*q^2) m).eval (13*q)

/-- The tail majorant of order `2m`. -/
def threeAtomTailBound (x : ℝ) (m : ℕ) : ℝ :=
  ((2*m).factorial:ℝ)*(8000*thetaCuspSourceTerm x 1^2*
    Real.exp (-(529/50)*thetaCuspSingleAtomReflectionScale 1 x))/(3/20)^(2*m)

theorem threeAtomTailBound_nonneg (x : ℝ) (m : ℕ) : 0 ≤ threeAtomTailBound x m := by
  unfold threeAtomTailBound; positivity

/-- **Pointwise three-atom lower bound** for the native odd fibre on the ray `q ≥ 3`. -/
theorem nativeOddForm_ge_threeAtom {x : ℝ} (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin 4 → ℝ) :
    4*thetaCuspSingleAtomReflectionScale 1 x^2*
        Real.exp (x-2*thetaCuspSingleAtomReflectionScale 1 x)*
        (∑ i : Fin 4, ∑ j : Fin 4, v i*v j*
          threeAtomOddEntry (thetaCuspSingleAtomReflectionScale 1 x) (i.val+j.val+1)) -
      ∑ i : Fin 4, ∑ j : Fin 4, |v i| * |v j| * threeAtomTailBound x (i.val+j.val+1) ≤
    ∑ i : Fin 4, ∑ j : Fin 4, v i*v j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x := by
  set q := thetaCuspSingleAtomReflectionScale 1 x with hqdef
  -- the diagonal pairs (2,2) and (3,3) are nonnegative
  have hd2 := atomPair_diag_oddFour_nonneg (a := 2) (by norm_num) (x := x)
    (by rw [scale_shift 2 (by norm_num) x]; push_cast; nlinarith) v
  have hd3 := atomPair_diag_oddFour_nonneg (a := 3) (by norm_num) (x := x)
    (by rw [scale_shift 3 (by norm_num) x]; push_cast; nlinarith) v
  -- the signed pair jets
  have hpair (a b : ℕ) (m : ℕ) : (-1:ℝ)^m*thetaCuspAtomPairReflectionJet (2*m) a b x =
      4*q^2*Real.exp (x-2*q)*((a:ℝ)^2*(b:ℝ)^2*Real.exp (-(((a:ℝ)^2+(b:ℝ)^2)-2)*q)*
        (thetaPairRadialEvenPolynomial ((a:ℝ)^2*(b:ℝ)^2*q^2) m).eval (((a:ℝ)^2+(b:ℝ)^2)*q)) := by
    rw [signed_pair_even]
    have he : Real.exp (x-((a:ℝ)^2+(b:ℝ)^2)*q) = Real.exp (x-2*q)*Real.exp (-(((a:ℝ)^2+(b:ℝ)^2)-2)*q) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he]; ring
  -- the tail
  have htail (m : ℕ) := native_threeAtom_cauchy_error (2*m) hq
  have hsplit : ∀ i j : Fin 4, v i*v j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x =
      v i*v j*(-1:ℝ)^(i.val+j.val+1)*thetaCuspThreeAtomReflectionJet (2*(i.val+j.val+1)) x +
      v i*v j*((-1:ℝ)^(i.val+j.val+1)*(thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x -
        thetaCuspThreeAtomReflectionJet (2*(i.val+j.val+1)) x)) := fun i j => by ring
  have hT : ∀ i j : Fin 4, -(|v i| * |v j| * threeAtomTailBound x (i.val+j.val+1)) ≤
      v i*v j*((-1:ℝ)^(i.val+j.val+1)*(thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x -
        thetaCuspThreeAtomReflectionJet (2*(i.val+j.val+1)) x)) := fun i j => by
    have h := htail (i.val+j.val+1)
    have habs : |v i*v j*((-1:ℝ)^(i.val+j.val+1)*(thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x -
        thetaCuspThreeAtomReflectionJet (2*(i.val+j.val+1)) x))| ≤
        |v i| * |v j| * threeAtomTailBound x (i.val+j.val+1) := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    exact neg_le_of_abs_le habs
  -- the three-atom part
  have hthree : ∀ i j : Fin 4, v i*v j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspThreeAtomReflectionJet (2*(i.val+j.val+1)) x =
      4*q^2*Real.exp (x-2*q)*(v i*v j*threeAtomOddEntry q (i.val+j.val+1)) +
      (v i*v j*(-1:ℝ)^(i.val+j.val+1)*thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) 2 2 x +
        v i*v j*(-1:ℝ)^(i.val+j.val+1)*thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) 3 3 x) := by
    intro i j
    rw [threeAtomJet_eq_sum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have p11 := hpair 1 1 (i.val+j.val+1); have p12 := hpair 1 2 (i.val+j.val+1)
    have p21 := hpair 2 1 (i.val+j.val+1); have p13 := hpair 1 3 (i.val+j.val+1)
    have p31 := hpair 3 1 (i.val+j.val+1); have p23 := hpair 2 3 (i.val+j.val+1)
    have p32 := hpair 3 2 (i.val+j.val+1)
    norm_num at p11 p12 p21 p13 p31 p23 p32
    unfold threeAtomOddEntry
    norm_num
    linear_combination v i*v j*(p11 + p12 + p21 + p13 + p31 + p23 + p32)
  have hsum : ∑ i : Fin 4, ∑ j : Fin 4, v i*v j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x =
      4*q^2*Real.exp (x-2*q)*(∑ i : Fin 4, ∑ j : Fin 4, v i*v j*threeAtomOddEntry q (i.val+j.val+1)) +
      ((∑ i : Fin 4, ∑ j : Fin 4, v i*v j*(-1:ℝ)^(i.val+j.val+1)*
          thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) 2 2 x) +
        (∑ i : Fin 4, ∑ j : Fin 4, v i*v j*(-1:ℝ)^(i.val+j.val+1)*
          thetaCuspAtomPairReflectionJet (2*(i.val+j.val+1)) 3 3 x)) +
      ∑ i : Fin 4, ∑ j : Fin 4, v i*v j*((-1:ℝ)^(i.val+j.val+1)*
        (thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x -
          thetaCuspThreeAtomReflectionJet (2*(i.val+j.val+1)) x)) := by
    simp only [hsplit, hthree, Finset.sum_add_distrib, Finset.mul_sum]
  have htot : -(∑ i : Fin 4, ∑ j : Fin 4, |v i| * |v j| * threeAtomTailBound x (i.val+j.val+1)) ≤
      ∑ i : Fin 4, ∑ j : Fin 4, v i*v j*((-1:ℝ)^(i.val+j.val+1)*
        (thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x -
          thetaCuspThreeAtomReflectionJet (2*(i.val+j.val+1)) x)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => hT i j
  rw [hsum]
  linarith

end
end RHTower.ThetaCuspOddFourThreeAtom
