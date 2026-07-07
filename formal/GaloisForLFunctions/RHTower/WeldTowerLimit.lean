/-
# The product tower survives the `P → ∞` limit past the wall — and reclaiming the strip is RH

`WeldTowerFree` shows the finite completed weld `archimedeanFactor · eulerPartial P` carries a free
coherent `2^k`-th root tower on the whole right half-plane `Re s > 0`.  `SeamReciprocity.completedSeam_eq`
identifies the `P → ∞` completed limit: for `Re s > 1`, `completedRiemannZeta s = archSeam s · seamDirichlet s`
with `seamDirichlet = Σ' n⁻ˢ = ζ` and `archSeam = π^(−s/2)Γ(s/2)`.  This file asks the honest question the
free finite weld opens: does the tower survive the limit, and where?

It survives — but the region contracts.  Both limiting factors stay nonvanishing only past the wall:
`archSeam` on `Re s > 0`, but `seamDirichlet = ζ` only on `Re s > 1` (its Euler product converges and is
zero-free there).  So the product `completedRiemannZeta` is a nonvanishing analytic unit on the *open*
half-plane `Re s > 1`, and inherits a free coherent `2^k`-th root tower there:

* `completedZeta_coherentTower_beyondWall` — the completed limit `completedRiemannZeta` has an
  unconditional coherent infinite Kummer tower on `Re s > 1`.
* `xi_coherentTower_beyondWall` — `ξ` (entire, zero-free on `Re s ≥ 1`) likewise carries an unconditional
  coherent tower on `Re s > 1`.

The free-tower region has thus contracted from `Re s > 0` (every finite weld) to `Re s > 1` (the completed
limit): the limit costs exactly the critical strip.  Reclaiming the last stretch — extending the tower from
`Re s > 1` down across the strip to `Re s > 1/2` — is precisely the Riemann Hypothesis:

* `rh_iff_xi_coherentTower_rightHalf` — RH holds **iff** `ξ` admits a coherent tower on `Re s > 1/2`.

This is exactly the edge where the free finite weld meets the conditional `ξ`: the tower is free through
the wall unconditionally, and its continuation across the strip is RH.  Nothing propagates it across the
strip; that continuation is the pinned constraint the whole ladder is about.
-/
import GaloisForLFunctions.RHTower.WeldTowerFree
import GaloisForLFunctions.RHTower.SeamReciprocity

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The open half-plane beyond the wall, `Re s > 1`. -/
def beyondWall : Set ℂ := {s : ℂ | 1 < s.re}

theorem isOpen_beyondWall : IsOpen beyondWall :=
  isOpen_lt continuous_const Complex.continuous_re

theorem convex_beyondWall : Convex ℝ beyondWall := convex_halfSpace_re_gt 1

theorem two_mem_beyondWall : (2 : ℂ) ∈ beyondWall := by
  show (1 : ℝ) < (2 : ℂ).re; norm_num

theorem isSimplyConnected_beyondWall : IsSimplyConnected beyondWall :=
  isSimplyConnected_of_convex convex_beyondWall ⟨2, two_mem_beyondWall⟩

/-! ### Free `2^k`-th root tower for a zero-free analytic unit on any open convex region -/

/-- **Free tower from nonvanishing on an open convex region.**  Any function analytic and nonvanishing
on an open, convex, nonempty (hence simply connected) set has a single-valued analytic `2^k`-th root
there. -/
theorem exists_pow_root_of_analyticOn_nonvanishing_convex (k : ℕ) {U : Set ℂ}
    (hUo : IsOpen U) (hUconv : Convex ℝ U) (hUne : U.Nonempty)
    {f : ℂ → ℂ} (hf : ∀ z ∈ U, AnalyticAt ℂ f z) (hne : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, g z ^ (2 ^ k) = f z := by
  have hdiff : DifferentiableOn ℂ f U := fun z hz => (hf z hz).differentiableWithinAt
  have h0 : (0 : ℂ) ∉ f '' U := by rintro ⟨z, hz, hzeq⟩; exact hne z hz hzeq
  exact Bottcher.exists_differentiableOn_pow_eq (isSimplyConnected_of_convex hUconv hUne)
    hUo hdiff h0 (pow_ne_zero k two_ne_zero)

/-- Package free roots at every level into the coherent-tower input, on an open convex region. -/
theorem coherentTower_of_analyticOn_nonvanishing_convex {U : Set ℂ} (hUo : IsOpen U)
    (hUconv : Convex ℝ U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) {f : ℂ → ℂ}
    (hf : ∀ z ∈ U, AnalyticAt ℂ f z) (hne : ∀ z ∈ U, f z ≠ 0) :
    Nonempty (CoherentTower f U) :=
  coherentTower_of_exists_roots_all_two_powers_preconnected hUo
    (isSimplyConnected_of_convex hUconv ⟨z₀, hz₀⟩) hUconv.isPreconnected hz₀
    (fun z hz => hf z hz) (hne z₀ hz₀)
    (fun k => by
      obtain ⟨g, hg, hgpow⟩ :=
        exists_pow_root_of_analyticOn_nonvanishing_convex k hUo hUconv ⟨z₀, hz₀⟩ hf hne
      exact ⟨g, hg.analyticOnNhd hUo, hgpow⟩)

/-! ### The completed limit survives past the wall -/

/-- The completed limit is nonvanishing beyond the wall: `completedRiemannZeta = archSeam · seamDirichlet`
with `archSeam ≠ 0` (`Re s > 0`) and `seamDirichlet = ζ ≠ 0` (`Re s > 1`). -/
theorem completedZeta_ne_zero_beyondWall {s : ℂ} (hs : s ∈ beyondWall) :
    completedRiemannZeta s ≠ 0 := by
  have hs1 : 1 < s.re := hs
  rw [completedSeam_eq hs1]
  refine mul_ne_zero (archimedeanFactor_ne_zero (by linarith)) ?_
  unfold seamDirichlet
  rw [← zeta_eq_tsum_one_div_nat_cpow hs1]
  exact riemannZeta_ne_zero_of_one_lt_re hs1

/-- The completed limit is analytic beyond the wall (its poles at `s = 0, 1` are on or left of the
wall). -/
theorem completedZeta_analyticAt_beyondWall {s : ℂ} (hs : s ∈ beyondWall) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have hdiff : DifferentiableOn ℂ completedRiemannZeta beyondWall := by
    intro z hz
    have hz1 : 1 < z.re := hz
    refine (differentiableAt_completedZeta ?_ ?_).differentiableWithinAt
    · rintro rfl; simp only [Complex.zero_re] at hz1; linarith
    · rintro rfl; simp only [Complex.one_re] at hz1; linarith
  exact (hdiff.analyticOnNhd isOpen_beyondWall) s hs

/-- **The completed limit survives the `P → ∞` boundary.**  `completedRiemannZeta` — the completed limit
`archSeam · seamDirichlet` of the finite welds — has an unconditional coherent infinite Kummer tower on
`Re s > 1`.  The product tower survives the limit, but only past the wall. -/
theorem completedZeta_coherentTower_beyondWall :
    Nonempty (CoherentTower completedRiemannZeta beyondWall) :=
  coherentTower_of_analyticOn_nonvanishing_convex isOpen_beyondWall convex_beyondWall
    two_mem_beyondWall (fun _ hz => completedZeta_analyticAt_beyondWall hz)
    (fun _ hz => completedZeta_ne_zero_beyondWall hz)

/-! ### ξ survives past the wall unconditionally; extending across the strip is RH -/

/-- **ξ survives past the wall.**  `ξ` (entire, zero-free on `Re s ≥ 1`) carries an unconditional
coherent infinite Kummer tower on `Re s > 1`. -/
theorem xi_coherentTower_beyondWall : Nonempty (CoherentTower xi beyondWall) :=
  coherentTower_of_analyticOn_nonvanishing_convex isOpen_beyondWall convex_beyondWall
    two_mem_beyondWall (fun z _ => xi_analyticOnNhd_univ z (Set.mem_univ z))
    (fun _ hz => xi_ne_zero_of_one_le_re (le_of_lt hz))

/-- **Reclaiming the strip is RH.**  The Riemann Hypothesis holds **iff** `ξ` admits a coherent infinite
Kummer tower on the full right half-plane `Re s > 1/2` — i.e. iff the free tower that survives past the
wall extends across the critical strip.  Forward and back through
`rh_iff_exists_roots_all_two_powers` and the coherent-tower/roots equivalence. -/
theorem rh_iff_xi_coherentTower_rightHalf :
    RiemannHypothesis ↔ Nonempty (CoherentTower xi rightHalf) := by
  rw [rh_iff_exists_roots_all_two_powers,
    coherentTower_iff_exists_roots_all_two_powers_preconnected isOpen_rightHalf
      (isSimplyConnected_of_convex convex_rightHalf ⟨2, two_mem_rightHalf⟩)
      convex_rightHalf.isPreconnected two_mem_rightHalf (xi_analyticOnNhd _) xi_two_ne_zero]

/-- **The survival dichotomy, packaged.**  For every `k` and every finite prime atlas `P`:

* the finite completed weld `archimedeanFactor · eulerPartial P` has a free `2^k`-th root on `Re s > 0`
  (unconditional);
* the completed limit `completedRiemannZeta` and `ξ` each carry a coherent tower on `Re s > 1`
  (unconditional — the tower survives the `P → ∞` limit past the wall);
* `ξ` carries a coherent tower on `Re s > 1/2` **iff** RH (the continuation across the strip is RH).

The free-tower region contracts from `Re s > 0` to `Re s > 1` at the limit; the last stretch across the
strip is the Riemann Hypothesis. -/
theorem weld_tower_survives_to_wall_extends_iff_rh (k : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    (∃ g : ℂ → ℂ, DifferentiableOn ℂ g rightHalfPlane ∧
        ∀ z ∈ rightHalfPlane, g z ^ (2 ^ k) = (archimedeanFactor * eulerPartial P) z)
    ∧ Nonempty (CoherentTower completedRiemannZeta beyondWall)
    ∧ Nonempty (CoherentTower xi beyondWall)
    ∧ (RiemannHypothesis ↔ Nonempty (CoherentTower xi rightHalf)) :=
  ⟨completedLocalFactor_pow_root k hP, completedZeta_coherentTower_beyondWall,
    xi_coherentTower_beyondWall, rh_iff_xi_coherentTower_rightHalf⟩

end

end RHTower

namespace RHTower
noncomputable section

/-! ### The threshold law: ξ's coherent tower on a half-plane = its zero-freeness there -/

/-- **The threshold law.**  For every real `σ`, `ξ` admits a coherent infinite Kummer tower on the open
half-plane `Re s > σ` **iff** `ξ` has no zero with `Re s > σ`.  The coherent-tower obstruction on any
half-plane is exactly its zero-set; the free tower survives down to the first zero and no further.  This
single statement subsumes both the unconditional survival past the wall (`σ = 1`) and RH (`σ = 1/2`). -/
theorem xi_coherentTower_iff_zeroFree_halfPlane (σ : ℝ) :
    Nonempty (CoherentTower xi {s : ℂ | σ < s.re}) ↔ ∀ s : ℂ, σ < s.re → xi s ≠ 0 := by
  set U : Set ℂ := {s : ℂ | σ < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := convex_halfSpace_re_gt σ
  set σ' : ℝ := max σ 1 + 1 with hσ'
  have hσ'σ : σ < σ' := lt_of_le_of_lt (le_max_left σ 1) (by linarith)
  have hσ'1 : (1 : ℝ) ≤ σ' := le_trans (le_max_right σ 1) (by linarith)
  have hz₀U : ((σ' : ℂ)) ∈ U := by show σ < ((σ' : ℂ)).re; rw [Complex.ofReal_re]; exact hσ'σ
  have hxiz₀ : xi ((σ' : ℂ)) ≠ 0 :=
    xi_ne_zero_of_one_le_re (by rw [Complex.ofReal_re]; exact hσ'1)
  constructor
  · intro htower s hs
    have hroots := (coherentTower_iff_exists_roots_all_two_powers_preconnected hUo
      (isSimplyConnected_of_convex hUconv ⟨_, hz₀U⟩) hUconv.isPreconnected hz₀U
      (fun z _ => xi_analyticOnNhd_univ z (Set.mem_univ z)) hxiz₀).mp htower
    exact nonvanishing_of_exists_roots_all_two_powers_preconnected hUo hUconv.isPreconnected hz₀U
      (fun z _ => xi_analyticOnNhd_univ z (Set.mem_univ z)) hxiz₀ hroots s hs
  · intro hzf
    exact coherentTower_of_analyticOn_nonvanishing_convex hUo hUconv hz₀U
      (fun z _ => xi_analyticOnNhd_univ z (Set.mem_univ z)) (fun z hz => hzf z hz)

/-- Unconditional corollary (`σ = 1`): `ξ` carries a coherent tower on `Re s > 1`. -/
theorem xi_coherentTower_gt_one : Nonempty (CoherentTower xi {s : ℂ | (1 : ℝ) < s.re}) :=
  (xi_coherentTower_iff_zeroFree_halfPlane 1).mpr fun _ hs => xi_ne_zero_of_one_le_re (le_of_lt hs)

/-- RH corollary (`σ = 1/2`): RH ⟺ `ξ` carries a coherent tower on `Re s > 1/2`. -/
theorem rh_iff_xi_coherentTower_gt_half :
    RiemannHypothesis ↔ Nonempty (CoherentTower xi {s : ℂ | (1 / 2 : ℝ) < s.re}) := by
  rw [rh_iff_xi_ne_zero_right, xi_coherentTower_iff_zeroFree_halfPlane (1 / 2)]
  rfl

end

end RHTower
