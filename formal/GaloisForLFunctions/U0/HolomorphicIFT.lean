/-
# Holomorphic implicit function theorem (Step 3 foundation)

For the u₀–φ_b independence proof, Step 3 (the algebraic implicit function theorem) needs: a
polynomial relation `P(z, u₀(z), φ_b(z)) = 0` forces `u₀` to continue analytically across a
boundary crossing point, contradicting the proven natural boundary (`U0NaturalBoundary`).

The analytic input is the **holomorphic implicit function theorem** at a simple root: the root
depends *analytically* on the parameter. In ℂ this is Mathlib's analytic-smoothness (`ω`) ContDiff
implicit function theorem (`ContDiffAt.implicitFunction` + `ContDiffAt.contDiffAt_implicitFunction`),
combined with `ContDiffAt.analyticAt` (analytic smoothness ⟹ analytic) — no Mathlib gap, and the
analyticity is automatic, not a separate bootstrapping.
-/
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Separation.Connected
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Separable

open Filter Topology Complex ContinuousLinearMap Set Polynomial
open scoped ContDiff

namespace HolomorphicIFT

/-- **Root-completeness (PROVEN).** Over ℂ, `d` distinct roots of a degree-`d` polynomial are *all*
its roots. (The roots multiset has card `d`; the `d` distinct roots fill its support.) This identifies
the `d` `holo_implicit` branches at a non-degenerate parameter with the complete root set, so any other
root — in particular `u₀(z)` — is one of the branches. -/
theorem root_complete {p : ℂ[X]} {d : ℕ} (hp : p ≠ 0) (hdeg : p.natDegree = d)
    {a : Fin d → ℂ} (hainj : Function.Injective a) (haroot : ∀ i, p.IsRoot (a i))
    {x : ℂ} (hx : p.IsRoot x) : ∃ i, x = a i := by
  have hcard : Multiset.card p.roots = d := by
    rw [← hdeg]; exact IsAlgClosed.card_roots_eq_natDegree
  have himg_sub : Finset.image a Finset.univ ⊆ p.roots.toFinset := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, mem_roots hp]; exact haroot i
  have himg_card : (Finset.image a Finset.univ).card = d := by
    rw [Finset.card_image_of_injective _ hainj, Finset.card_univ, Fintype.card_fin]
  have htf_card : p.roots.toFinset.card ≤ d := by
    rw [← hcard]; exact p.roots.toFinset_card_le
  have heq : Finset.image a Finset.univ = p.roots.toFinset :=
    Finset.eq_of_subset_of_card_le himg_sub (by rw [himg_card]; exact htf_card)
  have hxtf : x ∈ p.roots.toFinset := by rw [Multiset.mem_toFinset, mem_roots hp]; exact hx
  rw [← heq] at hxtf
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hxtf
  exact ⟨i, hi.symm⟩

/-- **The bivariate evaluation of `P ∈ ℂ[z][Y]` is analytic (PROVEN).** `(z,w) ↦ P(z, w)` (coefficients
of `P` evaluated at `z`, then as a polynomial in `w`) is a genuine bivariate polynomial, hence analytic
everywhere. This is the analytic relation `f` fed to `holo_implicit` in Step 3. -/
theorem bivar_analytic (P : Polynomial (Polynomial ℂ)) (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => P.eval₂ (Polynomial.evalRingHom q.1) q.2) p := by
  have heq : (fun q : ℂ × ℂ => P.eval₂ (Polynomial.evalRingHom q.1) q.2)
      = fun q : ℂ × ℂ => ∑ i ∈ Finset.range (P.natDegree + 1),
        (Polynomial.aeval q.1 (P.coeff i)) * q.2 ^ i := by
    funext q; rw [Polynomial.eval₂_eq_sum_range]; rfl
  rw [heq]
  exact Finset.analyticAt_fun_sum _
    (fun i _ => (analyticAt_fst.aeval_polynomial (P.coeff i)).mul (analyticAt_snd.pow i))

/-- **Partial `w`-derivative of the bivariate relation (PROVEN).** The directional derivative of
`f(z,w) = P(z,w)` in the `(0,1)` (pure-`w`) direction at `(z₀,w₀)` is the polynomial `w`-derivative
`(∂_Y P)(z₀, w₀)`. This is exactly the quantity `holo_implicit` needs nonzero: at a *simple* root `w₀`
of `P(z₀,·)` it is `(∂_Y P)(z₀,·)` evaluated at `w₀`, which is `≠ 0` precisely because the root is
simple. (Proof: restrict `f` to `{z₀}×ℂ`, whose derivative is the one-variable polynomial derivative;
match it to the `(0,1)` slice of the full Fréchet derivative by uniqueness.) -/
theorem partial_w_deriv (P : (Polynomial ℂ)[X]) (z₀ w₀ : ℂ) :
    (fderiv ℂ (fun q : ℂ × ℂ => P.eval₂ (evalRingHom q.1) q.2) (z₀, w₀)) (0, 1)
    = ((derivative P).map (evalRingHom z₀)).eval w₀ := by
  set f : ℂ × ℂ → ℂ := fun q => P.eval₂ (evalRingHom q.1) q.2 with hf
  have hfdiff : HasFDerivAt f (fderiv ℂ f (z₀, w₀)) (z₀, w₀) :=
    (bivar_analytic P (z₀, w₀)).differentiableAt.hasFDerivAt
  have hι : HasFDerivAt (fun w : ℂ => (z₀, w))
      ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) w₀ :=
    (hasFDerivAt_const z₀ w₀).prodMk (hasFDerivAt_id w₀)
  have hcomp : HasFDerivAt (fun w => f (z₀, w))
      ((fderiv ℂ f (z₀, w₀)).comp ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ))) w₀ :=
    hfdiff.comp w₀ hι
  have hpoly : HasDerivAt (fun w => f (z₀, w)) (((derivative P).map (evalRingHom z₀)).eval w₀) w₀ := by
    have hrw : (fun w => f (z₀, w)) = fun w => (P.map (evalRingHom z₀)).eval w := by
      funext w; simp only [hf]; rw [eval_map]
    rw [hrw]
    have hd := Polynomial.hasDerivAt (P.map (evalRingHom z₀)) w₀
    rw [Polynomial.derivative_map] at hd
    exact hd
  have huniq := hcomp.unique hpoly.hasFDerivAt
  have hev := ContinuousLinearMap.ext_iff.mp huniq 1
  simpa using hev

/-- **Separability over the fraction field ⟹ nonvanishing resultant (PROVEN).** If `P ∈ R[z][Y]`
becomes separable after base change to the fraction field `ℂ(z)` (the case of a minimal/irreducible
relation in characteristic 0), then `resultant(P, ∂_Y P) ∈ R[z]` is a *nonzero* polynomial. Its zero
locus is therefore finite — the bad set of parameters `z₀` where `P(z₀,·)` could fail to be squarefree.
The proof: separability = `IsCoprime P (∂P)` over the field, so the field resultant is nonzero
(`resultant_eq_zero_iff`); the resultant commutes with the (injective, degree-preserving) base-change
map (`resultant_map_map`), so the base-ring resultant is nonzero too. -/
theorem resultant_ne_zero_of_separable {R : Type*} [CommRing R] [IsDomain R]
    (P : R[X]) (hsep : (P.map (algebraMap R (FractionRing R))).Separable) :
    resultant P (derivative P) ≠ 0 := by
  set K := FractionRing R
  set φ := algebraMap R K with hφ
  have hφinj : Function.Injective φ := IsFractionRing.injective R K
  have hcop : IsCoprime (P.map φ) ((derivative P).map φ) := by
    have := hsep; rw [Separable, Polynomial.derivative_map] at this; exact this
  have hd1 : (P.map φ).natDegree = P.natDegree := natDegree_map_eq_of_injective hφinj P
  have hd2 : ((derivative P).map φ).natDegree = (derivative P).natDegree :=
    natDegree_map_eq_of_injective hφinj _
  intro h0
  have hz : φ (resultant P (derivative P)) = 0 := by rw [h0]; exact map_zero φ
  rw [← resultant_map_map φ (f := P) (g := derivative P)
      (m := P.natDegree) (n := (derivative P).natDegree)] at hz
  rw [← hd1, ← hd2] at hz
  rw [resultant_eq_zero_iff] at hz
  exact hz.2 hcop

/-- **Squarefree specialization at a good parameter (PROVEN).** At `z₀` where the two leading
coefficients and the resultant all survive evaluation, the specialized polynomial `P(z₀,·)` is
separable (squarefree). The specialized resultant equals `(resultant P P').eval z₀` — via
`resultant_map_map` and degree-preservation under evaluation (`natDegree_map_of_leadingCoeff_ne_zero`) —
so it is nonzero, hence `P(z₀,·)` and its derivative are coprime over ℂ. This delivers the
*simple-root* hypothesis that `holo_implicit` + `root_complete` consume in Step 3. -/
theorem separable_specialize {P : (Polynomial ℂ)[X]} (z₀ : ℂ)
    (hlead : P.leadingCoeff.eval z₀ ≠ 0)
    (hlead' : (derivative P).leadingCoeff.eval z₀ ≠ 0)
    (hres : (resultant P (derivative P)).eval z₀ ≠ 0) :
    (P.map (evalRingHom z₀)).Separable := by
  set ψ := evalRingHom z₀ with hψ
  have hd1 : (P.map ψ).natDegree = P.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ hlead
  have hd2 : ((derivative P).map ψ).natDegree = (derivative P).natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ hlead'
  have hPmap_ne : P.map ψ ≠ 0 := by
    intro h
    have hc : (P.map ψ).coeff P.natDegree = P.leadingCoeff.eval z₀ := by rw [coeff_map]; rfl
    rw [h, coeff_zero] at hc
    exact hlead hc.symm
  have key : resultant (P.map ψ) ((derivative P).map ψ) = (resultant P (derivative P)).eval z₀ := by
    have e := resultant_map_map ψ (f := P) (g := derivative P)
      (m := P.natDegree) (n := (derivative P).natDegree)
    rw [show resultant (P.map ψ) ((derivative P).map ψ)
          = resultant (P.map ψ) ((derivative P).map ψ) (P.map ψ).natDegree ((derivative P).map ψ).natDegree
        from rfl, hd1, hd2, e]
    rfl
  rw [Separable, Polynomial.derivative_map]
  by_contra hnc
  have hzero : resultant (P.map ψ) ((derivative P).map ψ) = 0 := by
    rw [resultant_eq_zero_iff]; exact ⟨Or.inl hPmap_ne, hnc⟩
  rw [key] at hzero
  exact hres hzero

/-- **A non-degenerate crossing point exists on the unit circle (PROVEN).** A nonzero polynomial has a
non-root on `{‖z‖ = 1}` (it has finitely many roots; the circle, being connected and nontrivial, is
infinite). Applied to the product of the leading coefficient and the discriminant, this supplies a
crossing point `z₀` where `P(z₀,·)` is non-degenerate (degree `d`, distinct roots) — the seed for the
branch construction in Step 3. -/
theorem exists_circle_non_root {p : ℂ[X]} (hp : p ≠ 0) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ p.eval z ≠ 0 := by
  have hroot_fin : {z : ℂ | p.eval z = 0}.Finite := by
    have : {z : ℂ | p.eval z = 0} = ↑p.roots.toFinset := by
      ext z; simp only [Set.mem_setOf_eq, Multiset.mem_toFinset, mem_roots hp, IsRoot,
        Finset.mem_coe]
    rw [this]; exact p.roots.toFinset.finite_toSet
  have hcirc_inf : (Metric.sphere (0:ℂ) 1).Infinite := by
    have hpre : IsPreconnected (Metric.sphere (0:ℂ) 1) :=
      (isConnected_sphere (by norm_num) (0:ℂ) (by norm_num)).isPreconnected
    refine hpre.infinite_of_nontrivial ⟨1, ?_, -1, ?_, by norm_num⟩ <;>
      simp [mem_sphere_zero_iff_norm]
  obtain ⟨z, hzc, hzr⟩ := (hcirc_inf.diff hroot_fin).nonempty
  rw [mem_sphere_zero_iff_norm] at hzc
  exact ⟨z, hzc, hzr⟩

/-- **A squarefree-specializing parameter exists on the unit circle (PROVEN).** Combining the two
halves: if `P ∈ ℂ[z][Y]` is separable over `ℂ(z)` (the minimal-relation case) and has positive
`Y`-degree, then there is a point `z₀` *on the unit circle* at which `P(z₀,·)` is squarefree. The bad
set is the zero locus of `P.leadingCoeff · (∂P).leadingCoeff · resultant(P,∂P)` — a nonzero polynomial
(`resultant_ne_zero_of_separable` + nonvanishing leading coefficients) — so it misses some circle point
(`exists_circle_non_root`). This is the exact entry point of Step 3: a crossing parameter with only
simple roots, where the holomorphic IFT gives `d` analytic branches and `u₀` must be one of them. -/
theorem exists_squarefree_specialization {P : (Polynomial ℂ)[X]}
    (hsep : (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable)
    (hdeg : 1 ≤ P.natDegree) :
    ∃ z₀ : ℂ, ‖z₀‖ = 1 ∧ P.leadingCoeff.eval z₀ ≠ 0 ∧ (P.map (evalRingHom z₀)).Separable := by
  have hP_ne : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; exact absurd hdeg (by norm_num)
  have hderiv_ne : derivative P ≠ 0 := by
    intro h
    have := natDegree_eq_zero_of_derivative_eq_zero h
    omega
  have hlc1 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP_ne
  have hlc2 : (derivative P).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hderiv_ne
  have hres : resultant P (derivative P) ≠ 0 := resultant_ne_zero_of_separable P hsep
  set q : ℂ[X] := P.leadingCoeff * (derivative P).leadingCoeff * resultant P (derivative P) with hq
  have hq_ne : q ≠ 0 := by rw [hq]; exact mul_ne_zero (mul_ne_zero hlc1 hlc2) hres
  obtain ⟨z₀, hz₀c, hz₀q⟩ := exists_circle_non_root hq_ne
  rw [hq, eval_mul, eval_mul] at hz₀q
  obtain ⟨hp1, hp3⟩ := mul_ne_zero_iff.mp hz₀q
  obtain ⟨hpa, hpb⟩ := mul_ne_zero_iff.mp hp1
  exact ⟨z₀, hz₀c, hpa, separable_specialize z₀ hpa hpb hp3⟩

/-- A set that lies in `𝓝[U] z` for each of its points equals `U ∩ O` for a global open `O`
(the union of witnessing open neighbourhoods). -/
theorem rel_open_eq {U S : Set ℂ} (hSU : S ⊆ U) (hS : ∀ z ∈ S, S ∈ 𝓝[U] z) :
    ∃ O, IsOpen O ∧ S = U ∩ O := by
  classical
  choose! V hVo hzV hVsub using fun z (hz : z ∈ S) => mem_nhdsWithin.mp (hS z hz)
  refine ⟨⋃ z ∈ S, V z, isOpen_biUnion (fun z hz => hVo z hz), ?_⟩
  apply Subset.antisymm
  · intro z hz; exact ⟨hSU hz, mem_biUnion hz (hzV z hz)⟩
  · rintro z ⟨hzU, hzO⟩
    obtain ⟨y, hy, hzVy⟩ := mem_iUnion₂.mp hzO
    exact hVsub y hy ⟨hzVy, hzU⟩

/-- **Locally-constant branch selection (PROVEN).** A continuous `h` on a preconnected set `U`, whose
value at each point is one of a *finite* family of pairwise-separated continuous branches `r i`, equals
a single branch `r j` on all of `U`. (The index is locally constant — `{h = r j}` and its complement
are both relatively open by separation — so it is constant on the connected `U`.)

This pins `u₀` to a single analytic root branch on the connected exterior near a crossing point — the
combinatorial half of Step 3's branch-matching. -/
theorem branch_selection {ι : Type*} [Fintype ι] {U : Set ℂ} (hU : IsPreconnected U)
    {h : ℂ → ℂ} {r : ι → ℂ → ℂ} (hUne : U.Nonempty)
    (hh : ContinuousOn h U) (hr : ∀ i, ContinuousOn (r i) U)
    (hsep : ∀ z ∈ U, ∀ i j, i ≠ j → r i z ≠ r j z)
    (hmem : ∀ z ∈ U, ∃ i, h z = r i z) :
    ∃ j, ∀ z ∈ U, h z = r j z := by
  classical
  obtain ⟨z₀, hz₀⟩ := hUne
  obtain ⟨j, hj⟩ := hmem z₀ hz₀
  refine ⟨j, ?_⟩
  have hne_loc : ∀ z ∈ U, ∀ i, r i z ≠ h z → ∀ᶠ w in 𝓝[U] z, h w ≠ r i w := by
    intro z hzU i hne
    have hsub : Tendsto (fun w => h w - r i w) (𝓝[U] z) (𝓝 (h z - r i z)) :=
      (hh.continuousWithinAt hzU).sub ((hr i).continuousWithinAt hzU)
    filter_upwards [hsub.eventually (eventually_ne_nhds (sub_ne_zero.mpr (Ne.symm hne)))] with w hw
    exact fun heq => hw (by rw [heq, sub_self])
  set S := {w ∈ U | h w = r j w} with hSdef
  have hSnhds : ∀ z ∈ S, S ∈ 𝓝[U] z := by
    rintro z ⟨hzU, hzeq⟩
    have hall : ∀ᶠ w in 𝓝[U] z, ∀ i, i ≠ j → h w ≠ r i w := by
      rw [eventually_all]
      intro i
      by_cases hij : i = j
      · exact Eventually.of_forall (fun w hh' => absurd hij hh')
      · filter_upwards [hne_loc z hzU i (by rw [hzeq]; exact hsep z hzU i j hij)] with w hw _ using hw
    filter_upwards [hall, self_mem_nhdsWithin] with w hw1 hwU
    refine ⟨hwU, ?_⟩
    obtain ⟨i, hi⟩ := hmem w hwU
    by_cases hij : i = j
    · rw [hi, hij]
    · exact absurd hi (hw1 i hij)
  have hTnhds : ∀ z ∈ U \ S, (U \ S) ∈ 𝓝[U] z := by
    rintro z ⟨hzU, hzns⟩
    have hzne : h z ≠ r j z := fun heq => hzns ⟨hzU, heq⟩
    filter_upwards [hne_loc z hzU j (Ne.symm hzne), self_mem_nhdsWithin] with w hw hwU
    exact ⟨hwU, fun hwS => hw hwS.2⟩
  obtain ⟨O₁, hO₁o, hO₁⟩ := rel_open_eq (fun z hz => hz.1) hSnhds
  obtain ⟨O₂, hO₂o, hO₂⟩ := rel_open_eq (fun z hz => hz.1) hTnhds
  intro z hzU
  by_contra hne
  have hzT : z ∈ U \ S := ⟨hzU, fun hzS => hne hzS.2⟩
  have hcover : U ⊆ O₁ ∪ O₂ := by
    intro w hwU
    rcases em (h w = r j w) with hw | hw
    · exact Or.inl ((hO₁ ▸ (⟨hwU, hw⟩ : w ∈ S)) : w ∈ U ∩ O₁).2
    · exact Or.inr ((hO₂ ▸ (⟨hwU, fun hwS => hw hwS.2⟩ : w ∈ U \ S)) : w ∈ U ∩ O₂).2
  have hz₀S : z₀ ∈ U ∩ O₁ := hO₁ ▸ (⟨hz₀, hj⟩ : z₀ ∈ S)
  have hzTO : z ∈ U ∩ O₂ := hO₂ ▸ hzT
  obtain ⟨w, hwU, hwO₁, hwO₂⟩ := hU O₁ O₂ hO₁o hO₂o hcover ⟨z₀, hz₀S⟩ ⟨z, hzTO⟩
  have hwS : w ∈ S := hO₁.symm ▸ (⟨hwU, hwO₁⟩ : w ∈ U ∩ O₁)
  have hwT : w ∈ U \ S := hO₂.symm ▸ (⟨hwU, hwO₂⟩ : w ∈ U ∩ O₂)
  exact hwT.2 hwS

/-- A continuous ℂ-linear endomorphism of ℂ is invertible as soon as its value at `1` is nonzero
(it is then scalar multiplication by that nonzero value). -/
theorem clm_invertible_of_apply_one_ne {g : ℂ →L[ℂ] ℂ} (hg : g 1 ≠ 0) : g.IsInvertible := by
  rw [show g = smulRight (1 : ℂ →L[ℂ] ℂ) (g 1) from by ext x; simp [← smul_eq_mul, ← map_smul]]
  exact ⟨(Units.mk0 (g 1) hg) • ContinuousLinearEquiv.refl ℂ ℂ,
    by ext x; simp [Units.smul_def]⟩

/-- **Holomorphic implicit function theorem (PROVEN).** For an analytic `f : ℂ×ℂ → ℂ` with
`f(z₀,w₀)=0` and nonzero partial `w`-derivative (`(fderiv f)(0,1) ≠ 0`, i.e. `∂_w f(z₀,w₀) ≠ 0`),
there is an **analytic** root branch `r` with `r z₀ = w₀` and `f(z, r z) = 0` near `z₀`.

Analyticity is obtained directly from the analytic-smoothness (`ω`) implicit function theorem, since
`ContDiffAt ℂ ω` ⟺ `AnalyticAt ℂ`. This is the local analytic continuation engine of Step 3: at a
simple root of an algebraic relation, the algebraic branch is analytic. -/
theorem holo_implicit {f : ℂ × ℂ → ℂ} {z₀ w₀ : ℂ}
    (hf : AnalyticAt ℂ f (z₀, w₀)) (h0 : f (z₀, w₀) = 0)
    (hfw : (fderiv ℂ f (z₀, w₀)) (0, 1) ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r z₀ ∧ r z₀ = w₀ ∧ (∀ᶠ z in 𝓝 z₀, f (z, r z) = 0) := by
  have cdf : ContDiffAt ℂ ω f (z₀, w₀) := hf.contDiffAt
  have if₂ : (fderiv ℂ f (z₀, w₀) ∘L (.inr ℂ ℂ ℂ)).IsInvertible :=
    clm_invertible_of_apply_one_ne (by simpa using hfw)
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  refine ⟨cdf.implicitFunction hω if₂,
    (cdf.contDiffAt_implicitFunction hω if₂).analyticAt, ?_, ?_⟩
  · exact cdf.implicitFunction_apply_self hω if₂
  · filter_upwards [cdf.eventually_apply_implicitFunction hω if₂] with z hz
    rw [hz, h0]

end HolomorphicIFT
