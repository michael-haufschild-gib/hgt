import GaloisForLFunctions.HTGeometry.FormalGermFiniteJetShadow

/-!
# Torsion rigidity for one-variable formal involutions

Over `ℂ`, a formal germ tangent to the identity cannot have order two unless it is the identity.
Consequently, two commuting involutions with derivative `-1` are equal: their composition is a
tangent-to-identity involution.  In particular, a commuting family of nonlinear one-variable
involutions cannot faithfully realize two independent quadratic gauge generators with the same
nontrivial tangent character.

The finite-jet theorem is proved directly from the first nonzero coefficient.  Passing through all
truncation orders gives the exact formal-germ statement, without convergence or analyticity
assumptions.
-/

open PowerSeries

namespace GaloisForLFunctions.FormalGerm

noncomputable section

private theorem tangent_order_eq_one {f : ℂ⟦X⟧}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) :
    f.order = 1 := by
  change f.order = ((1 : ℕ) : ℕ∞)
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · simp [hf1]
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hf0

private theorem coeff_tangent_pow_self {f : ℂ⟦X⟧}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (n : ℕ) :
    coeff n (f ^ n) = 1 := by
  have hforder : f.order = 1 := tangent_order_eq_one hf0 hf1
  have hftoNat : f.order.toNat = 1 := by rw [hforder]; rfl
  have hpoworder : (f ^ n).order.toNat = n := by
    rw [PowerSeries.order_pow, hforder]
    simp
  calc
    coeff n (f ^ n) = coeff (f ^ n).order.toNat (f ^ n) := by rw [hpoworder]
    _ = constantCoeff (PowerSeries.divXPowOrder (f ^ n)) := by
      rw [PowerSeries.constantCoeff_divXPowOrder]
    _ = constantCoeff ((PowerSeries.divXPowOrder f) ^ n) := by
      rw [PowerSeries.divXPowOrder_pow]
    _ = (constantCoeff (PowerSeries.divXPowOrder f)) ^ n := by simp
    _ = (coeff f.order.toNat f) ^ n := by
      rw [PowerSeries.constantCoeff_divXPowOrder]
    _ = 1 := by rw [hftoNat, hf1, one_pow]

private theorem coeff_subst_eq_self_of_tangent_of_first_nonzero
    {f u : ℂ⟦X⟧} (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    {n : ℕ} (huLower : ∀ d < n, coeff d u = 0) :
    coeff n (subst f u) = coeff n u := by
  have hsub : HasSubst f := HasSubst.of_constantCoeff_zero' hf0
  rw [PowerSeries.coeff_subst' hsub]
  rw [finsum_eq_single _ n]
  · rw [coeff_tangent_pow_self hf0 hf1]
    simp
  · intro d hdn
    by_cases hlt : d < n
    · rw [huLower d hlt]
      simp
    · have hgt : n < d := by omega
      have hforder : f.order = 1 := tangent_order_eq_one hf0 hf1
      have hpoworder : (f ^ d).order = d := by
        rw [PowerSeries.order_pow, hforder]
        simp
      have hcoeff : coeff n (f ^ d) = 0 := by
        apply PowerSeries.coeff_of_lt_order
        simpa [hpoworder] using hgt
      rw [hcoeff]
      simp

/-- A tangent-to-identity formal germ whose square is the identity modulo `X^M` is itself the
identity modulo `X^M`. -/
theorem tangentInvolution_mod_X_pow_eq_identity
    {f : ℂ⟦X⟧} (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    {M : ℕ} (hinv : (X : ℂ⟦X⟧) ^ M ∣ (subst f f - X)) :
    (X : ℂ⟦X⟧) ^ M ∣ (f - X) := by
  by_contra hnot
  have hnotall : ¬ ∀ n, n < M → coeff n (f - X) = 0 := by
    intro hall
    exact hnot (PowerSeries.X_pow_dvd_iff.mpr hall)
  push Not at hnotall
  let u : ℂ⟦X⟧ := f - X
  let n0 : ℕ := Nat.find hnotall
  have hn0M : n0 < M := (Nat.find_spec hnotall).1
  have hn0ne : coeff n0 u ≠ 0 := (Nat.find_spec hnotall).2
  have hn0Lower : ∀ d < n0, coeff d u = 0 := by
    intro d hd
    by_contra hdne
    have hle : n0 ≤ d := Nat.find_min' hnotall ⟨by omega, hdne⟩
    omega
  have hsub : HasSubst f := HasSubst.of_constantCoeff_zero' hf0
  have hdecomp : subst f f - X = u + subst f u := by
    have hf : f = X + u := by simp [u]
    calc
      subst f f - X = subst f (X + u) - X := by rw [hf]
      _ = (subst f X + subst f u) - X := by rw [subst_add hsub]
      _ = (f + subst f u) - X := by rw [subst_X hsub]
      _ = u + subst f u := by rw [hf]; ring
  have hcoeffZero := (PowerSeries.X_pow_dvd_iff.mp hinv) n0 hn0M
  rw [hdecomp, map_add] at hcoeffZero
  have hsubst : coeff n0 (subst f u) = coeff n0 u :=
    coeff_subst_eq_self_of_tangent_of_first_nonzero hf0 hf1 hn0Lower
  rw [hsubst] at hcoeffZero
  have htwo : (2 : ℂ) * coeff n0 u = 0 := by
    simpa [two_mul] using hcoeffZero
  exact hn0ne (by
    apply (mul_eq_zero.mp htwo).resolve_left
    norm_num)

private theorem coeff_one_subst_of_constantCoeff_zero
    {a f : ℂ⟦X⟧} (ha0 : constantCoeff a = 0) (hf0 : constantCoeff f = 0) :
    coeff 1 (subst a f) = coeff 1 f * coeff 1 a := by
  have hsub : HasSubst a := HasSubst.of_constantCoeff_zero' ha0
  rw [PowerSeries.coeff_subst' hsub]
  rw [finsum_eq_single _ 1]
  · simp
  · intro d hd
    obtain _ | d := d
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, hf0]
    obtain _ | d := d
    · exact False.elim (hd rfl)
    · simp [PowerSeries.coeff_one_pow, ha0]

/-- A genuine tangent-to-identity formal involution is the identity. -/
theorem tangentInvolution_eq_identity
    {f : ℂ⟦X⟧} (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (hinv : subst f f = X) :
    f = X := by
  apply PowerSeries.ext
  intro n
  have hinvdiv : (X : ℂ⟦X⟧) ^ (n + 1) ∣ (subst f f - X) := by
    rw [hinv, sub_self]
    exact dvd_zero _
  have hdiv : (X : ℂ⟦X⟧) ^ (n + 1) ∣ (f - X) :=
    tangentInvolution_mod_X_pow_eq_identity (M := n + 1) hf0 hf1 hinvdiv
  have hcoeff := (PowerSeries.X_pow_dvd_iff.mp hdiv) n (by omega)
  rw [map_sub, sub_eq_zero] at hcoeff
  exact hcoeff

/-- The composition of commuting formal involutions is again an involution. -/
private theorem subst_commuting_involutions_sq
    {f g : ℂ⟦X⟧} (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hfinv : subst f f = X) (hginv : subst g g = X)
    (hcomm : subst f g = subst g f) :
    subst (subst g f) (subst g f) = X := by
  have hsf : HasSubst f := HasSubst.of_constantCoeff_zero' hf0
  have hsg : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  have hfg0 : constantCoeff (subst g f) = 0 := constantCoeff_subst_eq_zero hg0 hf0
  have hsfg : HasSubst (subst g f) := HasSubst.of_constantCoeff_zero' hfg0
  calc
    subst (subst g f) (subst g f) = subst (subst (subst g f) g) f := by
      rw [PowerSeries.subst_comp_subst_apply hsg hsfg]
    _ = subst (subst g (subst f g)) f := by
      rw [PowerSeries.subst_comp_subst_apply hsf hsg]
    _ = subst (subst g (subst g f)) f := by rw [hcomm]
    _ = subst (subst (subst g g) f) f := by
      rw [PowerSeries.subst_comp_subst_apply hsg hsg]
    _ = subst f f := by rw [hginv, PowerSeries.X_subst]
    _ = X := hfinv

/-- Two commuting one-variable formal involutions with derivative `-1` are equal.  Their product
is tangent to the identity and has order two, hence torsion rigidity kills it. -/
theorem commutingFormalInvolutions_derivative_neg_one_eq
    {f g : ℂ⟦X⟧} (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf1 : coeff 1 f = -1) (hg1 : coeff 1 g = -1)
    (hfinv : subst f f = X) (hginv : subst g g = X)
    (hcomm : subst f g = subst g f) :
    f = g := by
  let h : ℂ⟦X⟧ := subst g f
  have hh0 : constantCoeff h = 0 := constantCoeff_subst_eq_zero hg0 hf0
  have hh1 : coeff 1 h = 1 := by
    change coeff 1 (subst g f) = 1
    rw [coeff_one_subst_of_constantCoeff_zero hg0 hf0, hf1, hg1]
    norm_num
  have hhinv : subst h h = X := subst_commuting_involutions_sq hf0 hg0 hfinv hginv hcomm
  have hh : h = X := tangentInvolution_eq_identity hh0 hh1 hhinv
  have hsubg : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  calc
    f = subst X f := by rw [PowerSeries.X_subst]
    _ = subst (subst g g) f := by rw [hginv]
    _ = subst g (subst g f) := by
      rw [PowerSeries.subst_comp_subst_apply hsubg hsubg]
    _ = subst g h := rfl
    _ = subst g X := by rw [hh]
    _ = g := by rw [PowerSeries.subst_X hsubg]

/-- A commuting family of nontrivial quadratic one-variable germs is constant. -/
theorem commutingFormalInvolutionFamily_derivative_neg_one_eq
    {I : Type*} (F : I → ℂ⟦X⟧)
    (h0 : ∀ i, constantCoeff (F i) = 0)
    (h1 : ∀ i, coeff 1 (F i) = -1)
    (hinv : ∀ i, subst (F i) (F i) = X)
    (hcomm : ∀ i j, subst (F i) (F j) = subst (F j) (F i))
    (i j : I) :
    F i = F j :=
  commutingFormalInvolutions_derivative_neg_one_eq
    (h0 i) (h0 j) (h1 i) (h1 j) (hinv i) (hinv j) (hcomm i j)

/-- Two distinct quadratic generators cannot be represented faithfully by commuting nonlinear
automorphisms of a one-variable formal germ when both have derivative `-1`. -/
theorem not_injective_commutingFormalInvolutionFamily_derivative_neg_one
    {I : Type*} (F : I → ℂ⟦X⟧)
    (h0 : ∀ i, constantCoeff (F i) = 0)
    (h1 : ∀ i, coeff 1 (F i) = -1)
    (hinv : ∀ i, subst (F i) (F i) = X)
    (hcomm : ∀ i j, subst (F i) (F j) = subst (F j) (F i))
    {i j : I} (hij : i ≠ j) :
    ¬ Function.Injective F := by
  intro hF
  exact hij (hF (commutingFormalInvolutionFamily_derivative_neg_one_eq
    F h0 h1 hinv hcomm i j))

end


end GaloisForLFunctions.FormalGerm
