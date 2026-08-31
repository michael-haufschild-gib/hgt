import GaloisForLFunctions.HTGeometry.RittTreeChannelNoRelation

/-!
# The Koenigs picture: a first-order relation for the linearizer is a cocycle

In the linearizer picture the shift is substitution by the map, `S : f ↦ f ∘ R`, the coordinate
field sits inside the germ field through `ι : ℂ(t) → L`, and the Koenigs equation is the eigen
relation `S κ = λ κ`.  The chain rule takes the twisted form `d ∘ S = ι(R′) · S ∘ d`.

Ritt's first-order relation for the linearizer, `(d κ)^r = A(t)·κ^j`, then becomes a rational
cocycle for the map: applying `S`, using `d(S κ) = λ d κ` and eliminating `κ^j`, gives

`A ∘ R · (R′)^r = λ^{r−j} · A`,

which is the affine transport equation with `k = r` and constant `λ^{r−j}`.  For an interior tree
channel that equation has no solution, so the linearizer satisfies no such relation.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {L : Type*} [Field L] [Algebra ℂ L]

noncomputable section

/-- **A first-order relation for the linearizer is a rational cocycle.** -/
theorem isRatAffineTransport_of_koenigs_relation
    (d : Derivation ℂ L L) (S : L →ₐ[ℂ] L) (ι : RatFunc ℂ →ₐ[ℂ] L)
    (hιinj : Function.Injective ι)
    {R : RatFunc ℂ} (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hSι : ∀ Q : RatFunc ℂ, S (ι Q) = ι (ratFuncSubstitutionAlgHom R hR Q))
    (hchain : ∀ x : L, d (S x) = ι (ratFuncDeriv R) * S (d x))
    {kap : L} {lam : ℂ} (hlam : lam ≠ 0) (hkap : kap ≠ 0)
    (hSkap : S kap = algebraMap ℂ L lam * kap)
    {A : RatFunc ℂ} (hA : A ≠ 0) {r j : ℤ} (hr : r ≠ 0)
    (hritt : (d kap) ^ r = ι A * kap ^ j) :
    IsRatAffineTransport R hR r (RatFunc.C (lam ^ (r - j))) 0 A := by
  have hlamL : algebraMap ℂ L lam ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℂ L).injective).mpr hlam
  have hιA : ι A ≠ 0 := fun h => hA (hιinj (by rw [h, map_zero]))
  have hkj : kap ^ j ≠ 0 := zpow_ne_zero j hkap
  have hdkap : d kap ≠ 0 := by
    intro h
    rw [h, zero_zpow r hr] at hritt
    exact (mul_ne_zero hιA hkj) hritt.symm
  -- the Koenigs equation differentiates to a scalar relation
  have hdS : d (S kap) = algebraMap ℂ L lam * d kap := by
    rw [hSkap, Derivation.leibniz]
    simp only [smul_eq_mul]
    rw [Derivation.map_algebraMap, mul_zero, add_zero]
  have hkey : algebraMap ℂ L lam * d kap = ι (ratFuncDeriv R) * S (d kap) := by
    rw [← hdS, hchain kap]
  have hιR : ι (ratFuncDeriv R) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hkey
    exact (mul_ne_zero hlamL hdkap) hkey
  have hRd : ratFuncDeriv R ≠ 0 := fun h => hιR (by rw [h, map_zero])
  have hSdkap : S (d kap) = algebraMap ℂ L lam * d kap / ι (ratFuncDeriv R) := by
    rw [eq_div_iff hιR]
    linear_combination -hkey
  -- transport the relation along the substitution
  have hkey2 := congrArg S hritt
  rw [map_zpow₀, map_mul, map_zpow₀, hSkap, hSι, hSdkap] at hkey2
  have hlamr : (algebraMap ℂ L lam) ^ r ≠ 0 := zpow_ne_zero r hlamL
  have hιRr : (ι (ratFuncDeriv R)) ^ r ≠ 0 := zpow_ne_zero r hιR
  have hexp : (algebraMap ℂ L lam * d kap / ι (ratFuncDeriv R)) ^ r
      = (algebraMap ℂ L lam) ^ r * ((d kap) ^ r / (ι (ratFuncDeriv R)) ^ r) := by
    rw [div_zpow, mul_zpow]
    ring
  rw [hexp, hritt, mul_zpow] at hkey2
  -- eliminate the power of the linearizer
  have hcancel : (algebraMap ℂ L lam) ^ r * (ι A / (ι (ratFuncDeriv R)) ^ r)
      = (algebraMap ℂ L lam) ^ j * ι (ratFuncSubstitutionAlgHom R hR A) := by
    have h := hkey2
    field_simp at h ⊢
    linear_combination h
  have hdesc : ι (RatFunc.C (lam ^ (r - j)) * A)
      = ι (ratFuncSubstitutionAlgHom R hR A * (ratFuncDeriv R) ^ r) := by
    have hC : ι (RatFunc.C (lam ^ (r - j))) = (algebraMap ℂ L lam) ^ (r - j) := by
      have h1 : (RatFunc.C (lam ^ (r - j)) : RatFunc ℂ)
          = algebraMap ℂ (RatFunc ℂ) (lam ^ (r - j)) := rfl
      rw [h1, AlgHom.commutes, map_zpow₀]
    have hDr : ι ((ratFuncDeriv R) ^ r) = (ι (ratFuncDeriv R)) ^ r := map_zpow₀ ι _ r
    have h2 : (algebraMap ℂ L lam) ^ r * ι A
        = (algebraMap ℂ L lam) ^ j * ι (ratFuncSubstitutionAlgHom R hR A)
          * (ι (ratFuncDeriv R)) ^ r := by
      have h3 := hcancel
      field_simp at h3
      linear_combination h3
    rw [map_mul, map_mul, hC, hDr, zpow_sub₀ hlamL, div_mul_eq_mul_div,
      div_eq_iff (zpow_ne_zero j hlamL)]
    linear_combination h2
  have hrat : RatFunc.C (lam ^ (r - j)) * A
      = ratFuncSubstitutionAlgHom R hR A * (ratFuncDeriv R) ^ r := hιinj hdesc
  rw [IsRatAffineTransport, add_zero]
  exact hrat.symm

/-- **The linearizer of an interior tree channel satisfies no first-order relation.** -/
theorem no_koenigs_relation_treeRG_interior {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1)
    (d : Derivation ℂ L L) (S : L →ₐ[ℂ] L) (ι : RatFunc ℂ →ₐ[ℂ] L)
    (hιinj : Function.Injective ι)
    {hR : ¬ ∃ c : ℂ, treeRG p (u : ℂ) (v : ℂ) = RatFunc.C c}
    (hSι : ∀ Q : RatFunc ℂ, S (ι Q)
      = ι (ratFuncSubstitutionAlgHom (treeRG p (u : ℂ) (v : ℂ)) hR Q))
    (hchain : ∀ x : L, d (S x) = ι (ratFuncDeriv (treeRG p (u : ℂ) (v : ℂ))) * S (d x))
    {kap : L} {lam : ℂ} (hlam : lam ≠ 0) (hkap : kap ≠ 0)
    (hSkap : S kap = algebraMap ℂ L lam * kap)
    {A : RatFunc ℂ} (hA : A ≠ 0) {r j : ℤ} (hr : r ≠ 0)
    (hritt : (d kap) ^ r = ι A * kap ^ j) : False := by
  have htrans := isRatAffineTransport_of_koenigs_relation d S ι hιinj hR hSι hchain hlam hkap
    hSkap hA hr hritt
  exact treeRG_no_cocycle_interior hp hv huv hu hr (zpow_ne_zero (r - j) hlam) hA htrans

end

end GaloisForLFunctions.HTGeometry
