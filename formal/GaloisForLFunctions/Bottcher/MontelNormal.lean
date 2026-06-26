/-
# Montel's theorem — normality of a uniformly bounded holomorphic family (sequential form)

The bounded-family **Montel theorem**: a sequence `F : ℕ → ℂ → ℂ` of functions holomorphic on
`ball c R` and uniformly bounded there (`‖F n z‖ ≤ C`) has a subsequence converging **uniformly on a
compact closed ball** `closedBall c r` (`r < R/2`) to a limit `g`, and the limit is **holomorphic** on
`ball c r`. This is the normality (`{F n}` is a normal family) at the heart of the Julia/Fatou
dichotomy that the connected-case `J_c` natural boundary runs on.

The proof assembles three mathlib facts on top of the equicontinuity brick of `Montel.lean`:
* the uniform Cauchy/Lipschitz equicontinuity (`equicontinuous_family_of_bounded`);
* the **Arzelà–Ascoli** theorem for bounded continuous functions
  (`BoundedContinuousFunction.arzela_ascoli`), giving a convergent subsequence in `K →ᵇ ℂ`;
* that a **locally uniform limit of holomorphic functions is holomorphic**
  (`TendstoLocallyUniformlyOn.differentiableOn`).

New file (Montel/Julia lane for the connected-case natural boundary); consumes `Montel`.
-/
import GaloisForLFunctions.Bottcher.Montel
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Complex Metric Set Filter Topology BoundedContinuousFunction

namespace Bottcher

/-- **Sequential Montel (normality of a uniformly bounded holomorphic family).** If each `F n` is
holomorphic on `ball c R` and `‖F n‖ ≤ C` there, then some subsequence `F ∘ φ` converges uniformly on
`closedBall c r` (`r < R/2`) to a limit `g` holomorphic on `ball c r`. -/
theorem montel_subseq {F : ℕ → ℂ → ℂ} {c : ℂ} {R C r : ℝ}
    (hr0 : 0 < r) (hrR : r < R / 2)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (ball c R))
    (hbd : ∀ n, ∀ z ∈ ball c R, ‖F n z‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoUniformlyOn (fun k => F (φ k)) g atTop (closedBall c r) ∧
      DifferentiableOn ℂ g (ball c r) := by
  classical
  have hR0 : 0 < R := by linarith
  haveI hcs : CompactSpace ↥(closedBall c r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
  have hsubR : closedBall c r ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hcont : ∀ n, ContinuousOn (F n) (closedBall c r) := fun n =>
    ((hF n).continuousOn).mono hsubR
  -- restrict each `F n` to a bounded continuous function on the compact ball
  let cmap : ℕ → C(↥(closedBall c r), ℂ) :=
    fun n => ⟨(closedBall c r).restrict (F n), (hcont n).restrict⟩
  let bcfF : ℕ → ↥(closedBall c r) →ᵇ ℂ := fun n => mkOfCompact (cmap n)
  have hval : ∀ n (x : ↥(closedBall c r)), bcfF n x = F n (x : ℂ) := fun n x => rfl
  -- equicontinuity of the ℕ-indexed family (Cauchy/Lipschitz, from `Montel.lean`)
  have hG0 : Equicontinuous (fun (n : ℕ) (p : ↥(closedBall c r)) => F n (p : ℂ)) :=
    equicontinuous_family_of_bounded hR0 hrR hF hbd
  set A : Set (↥(closedBall c r) →ᵇ ℂ) := Set.range bcfF with hA
  have hsec : ∀ a : ↥A, bcfF ((a.2).choose) = (a : ↥(closedBall c r) →ᵇ ℂ) :=
    fun a => (a.2).choose_spec
  -- the A-indexed coercion factors through `bcfF` via a section, so it is equicontinuous
  have hHcoe : ((↑) : ↥A → ↥(closedBall c r) → ℂ)
      = (fun (n : ℕ) (p : ↥(closedBall c r)) => F n (p : ℂ)) ∘ (fun a : ↥A => (a.2).choose) := by
    funext a x
    exact (DFunLike.congr_fun (hsec a) x).symm.trans (hval _ x)
  have hH : Equicontinuous ((↑) : ↥A → ↥(closedBall c r) → ℂ) := by
    rw [hHcoe]; exact hG0.comp _
  -- values land in the compact ball `closedBall 0 C`
  have hin : ∀ (f : ↥(closedBall c r) →ᵇ ℂ) (x : ↥(closedBall c r)),
      f ∈ A → f x ∈ closedBall (0 : ℂ) C := by
    intro f x hf
    obtain ⟨n, rfl⟩ := hf
    rw [mem_closedBall, dist_zero_right, hval n x]
    exact hbd n (x : ℂ) (hsubR x.2)
  -- Arzelà–Ascoli: the family is relatively compact in `K →ᵇ ℂ`
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) C)
      (isCompact_closedBall _ _) A hin hH
  have hmem : ∀ n, bcfF n ∈ closure A := fun n => subset_closure (mem_range_self n)
  obtain ⟨g, -, φ, hφmono, hφtends⟩ := hcompact.tendsto_subseq hmem
  -- convergence in `K →ᵇ ℂ` is uniform convergence on `K`
  have hunif := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly).mp hφtends
  simp only [Function.comp_apply] at hunif
  -- extend the limit `g` (a function on the subtype) to all of `ℂ`
  let G : ℂ → ℂ := fun z => if h : z ∈ closedBall c r then g ⟨z, h⟩ else 0
  have hGcoe : (G ∘ ((↑) : ↥(closedBall c r) → ℂ)) = (g : ↥(closedBall c r) → ℂ) := by
    funext x
    show (if h : (x : ℂ) ∈ closedBall c r then g ⟨(x : ℂ), h⟩ else 0) = g x
    rw [dif_pos x.2]
  have hfameq : (fun k => ((bcfF (φ k)) : ↥(closedBall c r) → ℂ))
      = (fun k (x : ↥(closedBall c r)) => F (φ k) (x : ℂ)) := by
    funext k x; exact hval (φ k) x
  rw [hfameq, ← hGcoe] at hunif
  have hUon : TendstoUniformlyOn (fun k => F (φ k)) G atTop (closedBall c r) :=
    (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).mpr hunif
  refine ⟨φ, G, hφmono, hUon, ?_⟩
  -- holomorphy of the limit
  have hlu : TendstoLocallyUniformlyOn (fun k => F (φ k)) G atTop (ball c r) :=
    (hUon.mono ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hdiff : ∀ᶠ k in atTop, DifferentiableOn ℂ (F (φ k)) (ball c r) :=
    Eventually.of_forall (fun k => (hF (φ k)).mono (ball_subset_ball (by linarith)))
  exact hlu.differentiableOn hdiff isOpen_ball

end Bottcher
