/-
# Böttcher tower — univalence of `f_c^[n]` on a depth-`n` cylinder (disconnected dynamical core)

The single remaining analytic input of the disconnected/disconnected case (STATUS.md "Disconnected
gap") is: `f_{c₁}^[n]` is univalent on a `K_{c₂}`-free annulus separating `z₀`'s depth-`n` Cantor
piece from the rest of `K_{c₁}`. Once that holds, the cylinder chart `φ̃_{c₁} = (φ_{c₁}∘f^[n])^{1/2ⁿ}`
exists and `CoverDeckScaling`'s chart→deck toolkit closes `hDisc`.

This file builds the **univalence engine**, the analytic heart of that statement, from the antipodal
structure of `f_c(z) = z²+c` (`f_c z = f_c w ↔ z = ±w`):

- `quadratic_injOn` — `f_c` is injective on any set `S` with no antipodal pair (`S ∩ (-S) ⊆ {0}`).
- `quadratic_iterate_injOn` — `f_c^[n]` is injective on `A` whenever `f_c` is injective on each
  forward image `f_c^[j] '' A` (`j < n`).

The depth-`n` cylinder's forward images each sit inside a single figure-eight lobe, and the two
lobes are exact antipodal images of one another (`f_c z = f_c (-z)`), so each lobe is antipodal-free
— which is exactly what `quadratic_iterate_injOn` consumes. Injectivity of `f_c^[n]` on the cylinder
makes its inverse branch single-valued around the full base circle, so the closed degree-1 lift
(`no_analytic_sqrt_iterate_of_closed_lift`) and the univalent chart both follow.
-/
import GaloisForLFunctions.Bottcher.BasinBranching
import GaloisForLFunctions.Bottcher.LiftConstruction
import GaloisForLFunctions.Bottcher.SquareFree
import Mathlib.Analysis.Complex.SqrtDeriv

open Complex Set Filter Topology

namespace Bottcher

/-- **`f_c = z²+c` is injective on any antipodal-pair-free set.** If `S` contains no genuine antipodal
pair — `z₁, z₂ ∈ S` with `z₁ = -z₂` forces `z₁ = z₂` (hence both `0`) — then `f_c` is injective on `S`.
Immediate from `f_c z₁ = f_c z₂ ↔ z₁² = z₂² ↔ (z₁-z₂)(z₁+z₂) = 0 ↔ z₁ = ±z₂`. The figure-eight lobes
are exact antipodal images (`f_c z = f_c (-z)`), so each lobe is antipodal-free and `f_c` is injective
on it. Axiom-clean. -/
theorem quadratic_injOn {c : ℂ} {S : Set ℂ}
    (hS : ∀ z₁ ∈ S, ∀ z₂ ∈ S, z₁ = -z₂ → z₁ = z₂) :
    Set.InjOn (quadratic c) S := by
  intro z₁ hz₁ z₂ hz₂ h
  have hsq : z₁ ^ 2 = z₂ ^ 2 := by simp only [quadratic] at h; linear_combination h
  have hfac : (z₁ - z₂) * (z₁ + z₂) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact sub_eq_zero.mp h1
  · exact hS z₁ hz₁ z₂ hz₂ (by linear_combination h2)

/-- **`f_c^[n]` is injective on `A` from step-wise antipodal-freeness.** If `f_c` is injective on every
forward image `f_c^[j] '' A` for `j < n`, then `f_c^[n]` is injective on `A`. Induction:
`f_c^[m+1] = f_c ∘ f_c^[m]`, with `f_c^[m]` injective on `A` (IH) and `f_c` injective on `f_c^[m] '' A`
(hypothesis), composed via `InjOn.comp`. The single remaining cylinder input becomes: each
`f_c^[j] '' A` lies in one figure-eight lobe (antipodal-free) for `j < n` — true for the depth-`n`
itinerary cylinder at level `t₀ ∈ (G_c(0)/2ⁿ, G_c(0)/2^{n-1})`, since then `f_c^[j] '' A` sits at
level `2ʲ t₀ < G_c(0)` for `j < n` (inside the sub-critical sublevel = the two lobes) while
`f_c^[n] '' A` reaches the far field. Axiom-clean. -/
theorem quadratic_iterate_injOn {c : ℂ} {A : Set ℂ} (n : ℕ)
    (h : ∀ j < n, Set.InjOn (quadratic c) ((quadratic c)^[j] '' A)) :
    Set.InjOn ((quadratic c)^[n]) A := by
  induction n with
  | zero => simp only [Function.iterate_zero]; exact Set.injOn_id A
  | succ m ih =>
    rw [Function.iterate_succ']
    have hm : Set.InjOn ((quadratic c)^[m]) A := ih (fun j hj => h j (by omega))
    have hf : Set.InjOn (quadratic c) ((quadratic c)^[m] '' A) := h m (by omega)
    exact hf.comp hm (Set.mapsTo_image _ _)

/-- **Antipodal-freeness from an open half-plane through `0`.** A set contained in `{z | 0 < re (a*z)}`
for some `a ≠ 0` has no antipodal pair: `0 < re(a z)` and `0 < re(a(-z)) = -re(a z)` are
contradictory. This is the concrete sufficient condition for `quadratic_injOn` — each figure-eight
lobe lies in such a half-plane (its points have one sign of `im (h ·)`, a half-plane in the
local saddle coordinate). Axiom-clean. -/
theorem antipodalFree_of_halfplane {S : Set ℂ} {a : ℂ}
    (hS : ∀ z ∈ S, 0 < (a * z).re) :
    ∀ z₁ ∈ S, ∀ z₂ ∈ S, z₁ = -z₂ → z₁ = z₂ := by
  intro z₁ hz₁ z₂ hz₂ heq
  have h1 : 0 < (a * z₁).re := hS z₁ hz₁
  have h2 : 0 < (a * z₂).re := hS z₂ hz₂
  rw [heq, mul_neg, Complex.neg_re] at h1
  linarith

/-- **A circle arc of angular extent `≤ π` is antipodal-free.** Any subset of the arc
`{circleMap 0 ρ θ | θ ∈ (α, α+π)}` (`ρ > 0`) contains no antipodal pair: the arc lies in the open
half-plane `{z | 0 < re(exp(-(α+π/2)i)·z)}` (the rotated `re > 0` half-plane, via
`cos(θ-(α+π/2)) > 0` on `(α,α+π)`), so `antipodalFree_of_halfplane` applies. This is the engine for
the depth-`k` cylinder's injectivity: the cylinder's forward images `f_c^[j] '' A` (`j<k`) are arcs of
angular extent `π/2^{k-j} ≤ π` (each `f_c` step doubles the angular extent of the previous arc, the
top one `f_c^[k-1] '' A` being a half-circle), hence antipodal-free, so `quadratic_iterate_injOn`
gives `f_c^[k]` injective on `A`. Axiom-clean. -/
theorem circleArc_antipodalFree {ρ α : ℝ} (hρ : 0 < ρ) {S : Set ℂ}
    (hS : S ⊆ (fun θ => circleMap 0 ρ θ) '' Set.Ioo α (α + Real.pi)) :
    ∀ z₁ ∈ S, ∀ z₂ ∈ S, z₁ = -z₂ → z₁ = z₂ := by
  apply antipodalFree_of_halfplane (a := Complex.exp (-(↑(α + Real.pi/2)) * Complex.I))
  intro z hz
  obtain ⟨θ, ⟨hθ1, hθ2⟩, rfl⟩ := hS hz
  have hexp : Complex.exp (-(↑(α + Real.pi/2)) * Complex.I) * circleMap 0 ρ θ
      = (↑ρ : ℂ) * Complex.exp (↑(θ - (α + Real.pi/2)) * Complex.I) := by
    simp only [circleMap, zero_add]
    rw [mul_comm, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hre : (Complex.exp (-(↑(α + Real.pi/2)) * Complex.I) * circleMap 0 ρ θ).re
      = ρ * Real.cos (θ - (α + Real.pi/2)) := by
    rw [hexp, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre]
  exact mul_pos hρ (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

end Bottcher

namespace Bottcher

open Complex Set Filter Topology

/-- **Iterate derivative is nonzero where the orbit avoids the critical point.** `(f_c^[n])'(z) =
∏_{j<n} 2·f_c^[j] z` is nonzero whenever no forward iterate `f_c^[j] z` (`j<n`) hits the critical
point `0`. The general form of `prod_two_mul_iterate_ne_zero_of_escapeOpen` — valid on the
sub-critical cylinder (which avoids the precritical orbit by its itinerary), not only on the far field.
Axiom-clean. -/
theorem prod_two_mul_iterate_ne_zero_of_orbit {c : ℂ} {z : ℂ} {n : ℕ}
    (h : ∀ j < n, (quadratic c)^[j] z ≠ 0) :
    (∏ j ∈ Finset.range n, 2 * (quadratic c)^[j] z) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  exact mul_ne_zero (by norm_num) (h j (Finset.mem_range.mp hj))

/-- **The preimage lift is continuous (injectivity + local inverse).** Let `f_c^[k]` be injective on
an open `A` avoiding the precritical orbit, and `γ` a section over a continuous base `β`
(`f_c^[k]∘γ = β`, `γ θ ∈ A`). Then `γ` is continuous at `θ₀`. Proof: at `z₀ = γ θ₀`, the iterate has a
local analytic inverse `ψ` (strict deriv `≠ 0`, `prod_two_mul_iterate_ne_zero_of_orbit`); near `θ₀`,
`ψ(β θ)` lies in `A` and is an `f_c^[k]`-preimage of `β θ`, so equals `γ θ` by injectivity — hence
`γ = ψ∘β` near `θ₀`, continuous. This is what upgrades a bare injective preimage map to the continuous
loop that `hasDerivAt_lift_of_continuousAt` then makes `C¹`: injectivity makes the inverse branch
single-valued around the WHOLE base, so the lift CLOSES. Axiom-clean. -/
theorem continuousAt_preimage_lift {c : ℂ} (k : ℕ) {A : Set ℂ} (hAo : IsOpen A)
    {β γ : ℝ → ℂ} {θ₀ : ℝ}
    (hβ : ContinuousAt β θ₀)
    (hγA : ∀ θ, γ θ ∈ A)
    (hinj : Set.InjOn ((quadratic c)^[k]) A)
    (hcrit : ∀ z ∈ A, ∀ j < k, (quadratic c)^[j] z ≠ 0)
    (hlift : ∀ θ, (quadratic c)^[k] (γ θ) = β θ) :
    ContinuousAt γ θ₀ := by
  set z₀ := γ θ₀ with hz₀def
  have hz₀A : z₀ ∈ A := hγA θ₀
  have hd : (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] z₀) ≠ 0 :=
    prod_two_mul_iterate_ne_zero_of_orbit (hcrit z₀ hz₀A)
  have hstrict : HasStrictDerivAt ((quadratic c)^[k])
      (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] z₀) z₀ :=
    hasStrictDerivAt_quadratic_iterate c k z₀
  set ψ := HasStrictDerivAt.localInverse _ _ _ hstrict hd with hψdef
  have hleft : ∀ᶠ x in 𝓝 z₀, ψ ((quadratic c)^[k] x) = x := hstrict.eventually_left_inverse hd
  have hright : ∀ᶠ w in 𝓝 ((quadratic c)^[k] z₀), (quadratic c)^[k] (ψ w) = w :=
    hstrict.eventually_right_inverse hd
  have hψcont : ContinuousAt ψ ((quadratic c)^[k] z₀) :=
    (hstrict.to_localInverse hd).hasDerivAt.continuousAt
  have hψz₀ : ψ ((quadratic c)^[k] z₀) = z₀ := by simpa using hleft.self_of_nhds
  have hψA : ∀ᶠ w in 𝓝 ((quadratic c)^[k] z₀), ψ w ∈ A := by
    have : ψ ((quadratic c)^[k] z₀) ∈ A := by rw [hψz₀]; exact hz₀A
    exact hψcont.eventually_mem (hAo.mem_nhds this)
  have hβz₀ : β θ₀ = (quadratic c)^[k] z₀ := (hlift θ₀).symm
  have hβtend : Tendsto β (𝓝 θ₀) (𝓝 ((quadratic c)^[k] z₀)) := by
    rw [← hβz₀]; exact hβ
  have hγeq : γ =ᶠ[𝓝 θ₀] (fun θ => ψ (β θ)) := by
    have h1 : ∀ᶠ θ in 𝓝 θ₀, (quadratic c)^[k] (ψ (β θ)) = β θ := hβtend.eventually hright
    have h2 : ∀ᶠ θ in 𝓝 θ₀, ψ (β θ) ∈ A := hβtend.eventually hψA
    filter_upwards [h1, h2] with θ hθ1 hθ2
    exact hinj (hγA θ) hθ2 (by rw [hlift θ, hθ1])
  exact (hψcont.comp_of_eq hβ hβz₀).congr hγeq.symm

end Bottcher

namespace Bottcher

open Complex Set Filter Topology

/-- **Loop-from-injectivity: injective `f_c^[k]` on a cylinder ⟹ no analytic square root.**
The mechanical heart of the loop route. If `f_c^[k]` is injective on an open `A` that avoids the
precritical orbit (`hcrit`) and escapes (`hesc`), and `γ` is any section of the base circle landing
in `A` (`f_c^[k]∘γ = C(0,R)`, `γ θ ∈ A`), then `φ_c∘f_c^[k]` has no analytic square root on `A`.
Injectivity is what makes the section's inverse branch single-valued around the WHOLE circle, so the
lift `γ` is automatically a CLOSED `C¹` loop (`continuousAt_preimage_lift` for continuity,
`hasDerivAt_lift_of_continuousAt` for the derivative, `hclosed` from `circleMap`'s period +
injectivity), and `no_analytic_sqrt_iterate_of_closed_lift` fires. This reduces the entire disconnected
non-squareness to a purely geometric statement: an open `A` near `z₀ ∈ K_{c₁}∖K_{c₂}` on which
`f_{c₁}^[k]` is injective (via `quadratic_iterate_injOn`), avoids `0`, escapes, and is `K_{c₂}`-free
— the depth-`k` cylinder. Axiom-clean. -/
theorem no_sqrt_of_inj_loop {c : ℂ} (k : ℕ) {R : ℝ} (hR : max 2 ‖c‖ < R)
    {A : Set ℂ} (hAo : IsOpen A) {γ : ℝ → ℂ}
    (hγA : ∀ θ, γ θ ∈ A)
    (hinj : Set.InjOn ((quadratic c)^[k]) A)
    (hcrit : ∀ z ∈ A, ∀ j < k, (quadratic c)^[j] z ≠ 0)
    (hesc : ∀ z ∈ A, (quadratic c)^[k] z ∈ escapeOpen c)
    (hlift : ∀ θ, (quadratic c)^[k] (γ θ) = circleMap 0 R θ)
    {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h A)
    (hsq : Set.EqOn (fun z => (h z) ^ 2) (fun z => bottcherCoord c ((quadratic c)^[k] z)) A) :
    False := by
  have hcq : Continuous (quadratic c) := by unfold quadratic; fun_prop
  have hβcont : Continuous (circleMap 0 R) := continuous_circleMap 0 R
  have hγcont : Continuous γ := by
    rw [continuous_iff_continuousAt]
    intro θ₀
    exact continuousAt_preimage_lift k hAo hβcont.continuousAt hγA hinj hcrit hlift
  set γ' : ℝ → ℂ := fun θ =>
    (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ θ))⁻¹ * deriv (circleMap 0 R) θ with hγ'def
  have hγd : ∀ θ, HasDerivAt γ (γ' θ) θ := by
    intro θ
    have hd : (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ θ)) ≠ 0 :=
      prod_two_mul_iterate_ne_zero_of_orbit (hcrit (γ θ) (hγA θ))
    have hstrict : HasStrictDerivAt ((quadratic c)^[k])
        (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ θ)) (γ θ) :=
      hasStrictDerivAt_quadratic_iterate c k (γ θ)
    have hcircderiv : HasDerivAt (circleMap 0 R) (deriv (circleMap 0 R) θ) θ :=
      (hasDerivAt_circleMap 0 R θ).differentiableAt.hasDerivAt
    have hev : (fun t => (quadratic c)^[k] (γ t)) =ᶠ[nhds θ] circleMap 0 R :=
      Filter.Eventually.of_forall hlift
    exact hasDerivAt_lift_of_continuousAt hstrict hd hγcont.continuousAt rfl hcircderiv hev
  have hvel : ∀ θ, deriv ((quadratic c)^[k]) (γ θ) * γ' θ = deriv (circleMap 0 R) θ := by
    intro θ
    have hd : (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ θ)) ≠ 0 :=
      prod_two_mul_iterate_ne_zero_of_orbit (hcrit (γ θ) (hγA θ))
    have hderiv : deriv ((quadratic c)^[k]) (γ θ)
        = ∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ θ) :=
      (hasStrictDerivAt_quadratic_iterate c k (γ θ)).hasDerivAt.deriv
    rw [hγ'def, hderiv]; dsimp only; field_simp
  have hγ'cont : Continuous γ' := by
    rw [hγ'def]
    have hderivc : Continuous (deriv (circleMap 0 R)) := by
      have heq : deriv (circleMap 0 R) = fun θ => circleMap 0 R θ * Complex.I := by
        funext θ; exact (hasDerivAt_circleMap 0 R θ).deriv
      rw [heq]; fun_prop
    apply Continuous.mul _ hderivc
    apply Continuous.inv₀
    · exact continuous_finsetProd _ (fun j _ =>
        continuous_const.mul ((hcq.iterate j).comp hγcont))
    · exact fun θ => prod_two_mul_iterate_ne_zero_of_orbit (hcrit (γ θ) (hγA θ))
  have hclosed : γ (2 * Real.pi) = γ 0 := by
    apply hinj (hγA _) (hγA _)
    rw [hlift, hlift]; simp [circleMap]
  exact no_analytic_sqrt_iterate_of_closed_lift k hR hAo hγcont hγ'cont hγA hγd hclosed
    hesc hlift hvel hh hsq

end Bottcher

namespace Bottcher

open Complex Set Filter Topology

/-- **`f_c(z) = z²+c` collapses antipodes.** `f_c(-z) = f_c z` (`(-z)² = z²`). The source of the
two-lobe antipodal symmetry of the disconnected basin. Axiom-clean. -/
theorem quadratic_neg (c z : ℂ) : quadratic c (-z) = quadratic c z := by
  simp only [quadratic, neg_sq]

/-- **Iterates of antipodes have equal modulus.** `‖f_c^[n](-z)‖ = ‖f_c^[n] z‖` for every `n`:
at `n=0` it is `‖-z‖=‖z‖`, and for `n≥1` the iterates are literally equal
(`f_c^[n](-z)=f_c^[n] z`, since `f_c(-z)=f_c z`). Axiom-clean. -/
theorem norm_iterate_neg (c z : ℂ) (n : ℕ) :
    ‖(quadratic c)^[n] (-z)‖ = ‖(quadratic c)^[n] z‖ := by
  cases n with
  | zero => simp
  | succ m => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, quadratic_neg]

/-- **`greenApprox` is even.** `greenApprox c (-z) n = greenApprox c z n` (from `norm_iterate_neg`). -/
theorem greenApprox_neg (c z : ℂ) (n : ℕ) : greenApprox c (-z) n = greenApprox c z n := by
  unfold greenApprox; rw [norm_iterate_neg]

/-- **The Green's function `G_c` is even: `G_c(-z) = G_c(z)`.** Pointwise limit of the even
`greenApprox`. So every sublevel set `{G_c < t}` is antipodal-symmetric (`z↦-z`), and the disconnected
figure-eight splits `{G_c < G_c 0}` into two lobes exchanged by `z↦-z` — the antipodal symmetry that
makes each lobe antipodal-free (and hence `f_c^[n]` injective on a depth-`n` itinerary cylinder, via
`quadratic_iterate_injOn`). Axiom-clean. -/
theorem greenLimit_neg (c z : ℂ) : greenLimit c (-z) = greenLimit c z := by
  unfold greenLimit
  congr 1
  funext n
  exact greenApprox_neg c z n

/-- **Disjoint-from-antipode ⟹ antipodal-free (the lobe injectivity hook).** If `S` is disjoint from
its antipodal image `-S` (`Disjoint S (-S)`, e.g. a single figure-eight lobe `L` with `-L` the other
lobe), then `S` has no antipodal pair, so `quadratic_injOn` gives `f_c` injective on `S`. This is the
set-level form feeding the depth-`n` cylinder: each `f_c^[j] '' A` lies in one lobe `L_{σ_j}` with
`L_{σ_j}` disjoint from `-L_{σ_j} = L_{-σ_j}`. Axiom-clean. -/
theorem antipodalFree_of_disjoint_neg {S : Set ℂ} (h : Disjoint S (-S : Set ℂ)) :
    ∀ z₁ ∈ S, ∀ z₂ ∈ S, z₁ = -z₂ → z₁ = z₂ := by
  intro z₁ hz₁ z₂ hz₂ heq
  exact absurd (Set.mem_inter hz₁ (by rw [Set.mem_neg, heq, neg_neg]; exact hz₂))
    (by rw [Set.disjoint_iff] at h; exact fun hc => h hc)

end Bottcher

namespace Bottcher

open Complex Set

/-- **`Complex.sqrt` squares back (unconditional).** `(Complex.sqrt z)^2 = z` for every `z`, since
`Complex.sqrt z = z^(2⁻¹)` and `(z^(2⁻¹))^2 = z` (`cpow_nat_inv_pow`). Axiom-clean. -/
theorem complex_sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  rw [Complex.sqrt, show (2 : ℂ)⁻¹ = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  exact Complex.cpow_nat_inv_pow z (by norm_num)

/-- **`±√(w-c)` are the two inverse branches of `f_c`.** `f_c(±√(w-c)) = w` (from `complex_sqrt_sq`):
`(±√(w-c))² + c = (w-c) + c = w`. The two depth-1 preimages of `w`, negatives of one another — the
source of the two-lobe antipodal split. Axiom-clean. -/
theorem quadratic_sqrt_inverse (c w : ℂ) :
    quadratic c (Complex.sqrt (w - c)) = w ∧ quadratic c (-(Complex.sqrt (w - c))) = w := by
  have h : (Complex.sqrt (w - c)) ^ 2 = w - c := complex_sqrt_sq (w - c)
  constructor <;> · simp only [quadratic, neg_sq]; rw [h]; ring

/-- **Holomorphic inverse branches of `f_c` on a slit plane.** On `U_c = {w | w - c ∈ slitPlane}`
(a simply-connected domain avoiding the critical value `c`), `s_+(w) = √(w-c)` and `s_-(w) = -√(w-c)`
are holomorphic, satisfy `f_c ∘ s_± = id`, and are negatives (`s_- = -s_+`) — so their images are
antipodal (one lobe and its `z↦-z` reflection). This is the lobe-construction engine: composing these
branches along an itinerary builds the depth-`n` cylinder (each branch univalent ⟹ `f_c^[n]` injective
on the composite image, no Koebe needed — mathlib `differentiableOn_sqrt` + `complex_sqrt_sq`).
Axiom-clean. -/
theorem quadratic_inverse_branch_slit (c : ℂ) :
    DifferentiableOn ℂ (fun w => Complex.sqrt (w - c)) {w | w - c ∈ slitPlane} ∧
    (∀ w ∈ {w | w - c ∈ slitPlane}, quadratic c (Complex.sqrt (w - c)) = w) := by
  refine ⟨Complex.differentiableOn_sqrt.comp (by fun_prop) (fun w hw => hw), ?_⟩
  intro w _
  exact (quadratic_sqrt_inverse c w).1

end Bottcher

namespace Bottcher

open Complex Set Metric

/-- **Round annulus = `exp` of a vertical strip.** For `0 < r < R`,
`{t | r < ‖t‖ < R} = exp '' {s | log r < re s < log R}` (`‖exp s‖ = exp(re s)`). Axiom-clean. -/
theorem annulus_eq_exp_strip {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    {t : ℂ | r < ‖t‖ ∧ ‖t‖ < R} = Complex.exp '' {s : ℂ | Real.log r < s.re ∧ s.re < Real.log R} := by
  have hRpos : 0 < R := lt_trans hr hR
  ext t
  simp only [mem_setOf_eq, mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    have ht0 : t ≠ 0 := by rintro rfl; simp only [norm_zero] at h1; linarith
    have htpos : 0 < ‖t‖ := by positivity
    refine ⟨Complex.log t, ⟨?_, ?_⟩, Complex.exp_log ht0⟩
    · rw [Complex.log_re]; exact Real.log_lt_log hr h1
    · rw [Complex.log_re]; exact Real.log_lt_log htpos h2
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    rw [Complex.norm_exp]
    refine ⟨?_, ?_⟩
    · calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
        _ < Real.exp s.re := Real.exp_lt_exp.mpr h1
    · calc Real.exp s.re < Real.exp (Real.log R) := Real.exp_lt_exp.mpr h2
        _ = R := Real.exp_log hRpos

/-- **A round annulus is connected** (`0 < r < R`): the continuous image of the convex (hence
connected) strip `{log r < re s < log R}` under `exp`. The cover-annulus carrier `U` is such an
annulus; `IsPreconnected U` is what `monoF_witness_projection_base` requires. Axiom-clean. -/
theorem isConnected_annulus {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    IsConnected {t : ℂ | r < ‖t‖ ∧ ‖t‖ < R} := by
  have hmid : 0 < (r + R) / 2 := by linarith
  rw [annulus_eq_exp_strip hr hrR]
  apply IsConnected.image
  · apply Convex.isConnected
    · exact (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
    · refine ⟨Real.log ((r+R)/2), ?_, ?_⟩
      · show Real.log r < (Real.log ((r+R)/2) : ℂ).re
        rw [Complex.ofReal_re]; exact Real.log_lt_log hr (by linarith)
      · show ((Real.log ((r+R)/2) : ℂ)).re < Real.log R
        rw [Complex.ofReal_re]; exact Real.log_lt_log hmid (by linarith)
  · exact Complex.continuous_exp.continuousOn

/-- **The rotation deck FIXES every function of `t^{2ⁿ}`** when `ζ₀^{2ⁿ}=1` — the projection `p₀` and
`a₂ = φ_{c₂}∘p₀` of the cover-annulus model both factor through `t^{2ⁿ} = φ̃_{c₁}^{2ⁿ}`, so are
deck-invariant. This is the concrete mechanism (`(ζ₀t)^{2ⁿ} = ζ₀^{2ⁿ}·t^{2ⁿ} = t^{2ⁿ}`) by which the
SAME deck that scales `a₁ = φ̃_{c₁}` (the `t`-coordinate) leaves `p₀` and `φ_{c₂}` fixed — the
resolution of the planar-deck obstruction (the cover `U` is in the `t`-coordinate, the `z`-projection
factors through `t^{2ⁿ}`). Axiom-clean. -/
theorem rotation_fixes_monomial_comp {ζ₀ : ℂ} {n : ℕ} (hζpow : ζ₀ ^ (2 ^ n) = 1)
    (h : ℂ → ℂ) (t : ℂ) :
    (fun s => h (s ^ (2 ^ n))) (ζ₀ * t) = (fun s => h (s ^ (2 ^ n))) t := by
  simp only [mul_pow, hζpow, one_mul]

end Bottcher

namespace Bottcher

open Complex Set

/-- **`exp` is injective on a horizontal strip of height `≤ 2π`.** If `im a, im b ∈ (y₀, y₀+2π]` and
`exp a = exp b` then `a = b` — `exp` periodicity forces the period multiple `n` to vanish
(`|a.im - b.im| ≤ 2π` and `= |n|·2π` with `n∈ℤ` ⟹ `n=0`). The engine for univalence of the dyadic
lift `φ̃_{c₁} = exp(2⁻ⁿ·bottcherLog∘f^[n])`: on a single cover sheet (`im` of the log-argument
spanning one period) `exp` does not wrap, so `φ̃_{c₁}` inherits injectivity from
`2⁻ⁿ·bottcherLog∘f^[n]`. Axiom-clean. -/
theorem exp_injOn_strip {y₀ : ℝ} :
    Set.InjOn Complex.exp {z : ℂ | y₀ < z.im ∧ z.im ≤ y₀ + 2 * Real.pi} := by
  intro a ⟨ha1, ha2⟩ b ⟨hb1, hb2⟩ hab
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hab
  have him : a.im = b.im + (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re] at this
    simpa using this
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · exfalso; have hc : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      nlinarith [him]
    · exact h
    · exfalso; have hc : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith [him]
  rw [hn0] at hn; simpa using hn

/-- **`exp ∘ g` is injective from `g` injective into a height-`≤2π` strip.** Composition of the
injective `g` with `exp` (injective on the strip, `exp_injOn_strip`). With `g = 2⁻ⁿ·bottcherLog∘f^[n]`
this yields univalence of `φ̃_{c₁}` on a cover sheet — the chart `chart_deck_*` and the deck route
consume. Axiom-clean. -/
theorem exp_comp_injOn {α : Type*} {g : α → ℂ} {D : Set α} {y₀ : ℝ}
    (hg : Set.InjOn g D) (hmaps : ∀ x ∈ D, y₀ < (g x).im ∧ (g x).im ≤ y₀ + 2 * Real.pi) :
    Set.InjOn (fun x => Complex.exp (g x)) D :=
  fun a ha b hb hab => hg ha hb (exp_injOn_strip (hmaps a ha) (hmaps b hb) hab)

end Bottcher
