import GaloisForLFunctions.HTGeometry.EllipticEvenRationalWeierstrass

/-!
# Every elliptic function is rational in `℘` and `℘'`

The structure theorem for elliptic functions: a meromorphic function on `ℂ` invariant under a period
lattice satisfies

`C(℘) · f = A(℘) + ℘' · B(℘)`

for polynomials `A`, `B` and a monic `C`, as an identity of meromorphic germs at every point.

The even part of `f` and the quotient of its odd part by `℘'` are both even elliptic functions,
hence rational in `℘`; multiplying by the two denominators gives the displayed identity.  The
quotient by `℘'` is legitimate because `℘'` is not locally constant equal to zero: it has a pole of
order three at every lattice point.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable (L : PeriodPair)

/-- `℘'` has a pole of order three at the origin. -/
theorem meromorphicOrderAt_derivWeierstrassP_zero :
    meromorphicOrderAt L.derivWeierstrassP 0 = ((-3 : ℤ) : WithTop ℤ) := by
  have hord : meromorphicOrderAt L.weierstrassP 0 = ((-2 : ℤ) : WithTop ℤ) := by
    rw [L.order_weierstrassP 0 (zero_mem_lattice L)]
    norm_num
  have hne : ((-2 : ℤ) : ℂ) ≠ 0 := by norm_num
  have h := meromorphicOrderAt_deriv_eq_sub_one hne hord
  rw [L.deriv_weierstrassP] at h
  rw [h]
  norm_num

/-- `℘'` is nowhere locally zero. -/
theorem meromorphicOrderAt_derivWeierstrassP_ne_top (z : ℂ) :
    meromorphicOrderAt L.derivWeierstrassP z ≠ ⊤ := by
  have hmerOn : MeromorphicOn L.derivWeierstrassP Set.univ :=
    fun w _ => L.meromorphic_derivWeierstrassP w
  have hzero : meromorphicOrderAt L.derivWeierstrassP 0 ≠ ⊤ := by
    rw [meromorphicOrderAt_derivWeierstrassP_zero]
    simp
  exact hmerOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ _) (Set.mem_univ z) hzero

/-- Near every point `℘'` is eventually nonzero. -/
theorem eventually_derivWeierstrassP_ne_zero (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, L.derivWeierstrassP w ≠ 0 :=
  (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (L.meromorphic_derivWeierstrassP z)).mp
    (meromorphicOrderAt_derivWeierstrassP_ne_top L z)

section

variable {f : ℂ → ℂ} (hmer : ∀ z, MeromorphicAt f z)
  (hper : ∀ p ∈ L.lattice, Function.Periodic f p)

include hmer in
/-- The reflection of a meromorphic function is meromorphic. -/
theorem meromorphicAt_comp_neg (z : ℂ) : MeromorphicAt (fun w => f (-w)) z := by
  have hcomp : MeromorphicAt (f ∘ fun w : ℂ => -w) z :=
    MeromorphicAt.comp_analyticAt (f := f) (g := fun w : ℂ => -w) (hmer (-z)) (by fun_prop)
  exact hcomp

include hper in
/-- The reflection of a lattice-periodic function is lattice-periodic. -/
theorem comp_neg_add_eq {p : ℂ} (hp : p ∈ L.lattice) (w : ℂ) : f (-(w + p)) = f (-w) := by
  have hnegp : -p ∈ L.lattice := Submodule.neg_mem _ hp
  have hshift := hper (-p) hnegp (-w)
  have hrw : -w + -p = -(w + p) := by ring
  rw [hrw] at hshift
  exact hshift

include hmer hper in
/-- **The structure theorem for elliptic functions.**  A lattice-periodic meromorphic function on
`ℂ` is a rational function of `℘` and `℘'`, with `℘'` occurring to the first power only. -/
theorem exists_rational_weierstrass_representation :
    ∃ A B C : Polynomial ℂ, C.Monic ∧
      ∀ z : ℂ, (fun w => f w * C.eval (L.weierstrassP w)) =ᶠ[𝓝[≠] z]
        fun w => A.eval (L.weierstrassP w)
          + L.derivWeierstrassP w * B.eval (L.weierstrassP w) := by
  obtain ⟨fe, hfe⟩ : ∃ fe : ℂ → ℂ, ∀ w, fe w = (f w + f (-w)) / 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨fo, hfo⟩ : ∃ fo : ℂ → ℂ, ∀ w, fo w = (f w - f (-w)) / 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, ∀ w, g w = fo w / L.derivWeierstrassP w := ⟨_, fun _ => rfl⟩
  have hnegmer : ∀ z, MeromorphicAt (fun w => f (-w)) z := meromorphicAt_comp_neg hmer
  have hfemer : ∀ z, MeromorphicAt fe z := by
    intro z
    refine MeromorphicAt.congr ?_ (Filter.Eventually.of_forall fun w => (hfe w).symm)
    exact ((hmer z).add (hnegmer z)).div (MeromorphicAt.const 2 z)
  have hfomer : ∀ z, MeromorphicAt fo z := by
    intro z
    refine MeromorphicAt.congr ?_ (Filter.Eventually.of_forall fun w => (hfo w).symm)
    exact ((hmer z).sub (hnegmer z)).div (MeromorphicAt.const 2 z)
  have hgmer : ∀ z, MeromorphicAt g z := by
    intro z
    refine MeromorphicAt.congr ?_ (Filter.Eventually.of_forall fun w => (hgdef w).symm)
    exact (hfomer z).div (L.meromorphic_derivWeierstrassP z)
  have hfeper : ∀ p ∈ L.lattice, Function.Periodic fe p := by
    intro p hp w
    rw [hfe, hfe, hper p hp w, comp_neg_add_eq L hper hp w]
  have hfoper : ∀ p ∈ L.lattice, Function.Periodic fo p := by
    intro p hp w
    rw [hfo, hfo, hper p hp w, comp_neg_add_eq L hper hp w]
  have hgper : ∀ p ∈ L.lattice, Function.Periodic g p := by
    intro p hp w
    rw [hgdef, hgdef, hfoper p hp w, L.periodic_derivWeierstrassP ⟨p, hp⟩ w]
  have hfeeven : ∀ w : ℂ, fe (-w) = fe w := by
    intro w
    rw [hfe, hfe, neg_neg]
    ring
  have hgeven : ∀ w : ℂ, g (-w) = g w := by
    intro w
    rw [hgdef, hgdef, hfo, hfo, neg_neg, L.derivWeierstrassP_neg w,
      show ((f (-w) - f w) / 2) = -((f w - f (-w)) / 2) by ring, neg_div_neg_eq]
  obtain ⟨P₁, Q₁, hQ₁, hrep₁⟩ :=
    exists_rational_eval_weierstrassP_of_even L hfemer hfeper hfeeven
  obtain ⟨P₂, Q₂, hQ₂, hrep₂⟩ :=
    exists_rational_eval_weierstrassP_of_even L hgmer hgper hgeven
  refine ⟨P₁ * Q₂, P₂ * Q₁, Q₁ * Q₂, hQ₁.mul hQ₂, fun z => ?_⟩
  filter_upwards [hrep₁ z, hrep₂ z, eventually_derivWeierstrassP_ne_zero L z] with w hw₁ hw₂ hwne
  have hsplit : f w = fe w + L.derivWeierstrassP w * g w := by
    rw [hgdef, hfe, hfo]
    field_simp
    ring
  simp only [Polynomial.eval_mul]
  rw [hsplit]
  have hexp : (fe w + L.derivWeierstrassP w * g w)
      * (Q₁.eval (L.weierstrassP w) * Q₂.eval (L.weierstrassP w))
      = (fe w * Q₁.eval (L.weierstrassP w)) * Q₂.eval (L.weierstrassP w)
        + L.derivWeierstrassP w
          * ((g w * Q₂.eval (L.weierstrassP w)) * Q₁.eval (L.weierstrassP w)) := by
    ring
  rw [hexp, hw₁, hw₂]

end

end GaloisForLFunctions.HTGeometry
