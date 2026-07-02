/-
# P5 capstone: a relation forces a rel-open smooth Julia piece at a hole-free tip

The full pigeonhole chain, assembled.  For connected nonexceptional parameters and a hole-free
tip (open problem 04, answered), an assumed bivariate relation between the Böttcher coordinates
produces a **relatively open piece of `J₁` inside the modulus-one locus of one continuous root
branch**: the minimal separable relation (`RelativeMinimalRelation`) has a far-field witness; the
countable-avoidance mover (`RelativeFibreGeneric`) relocates it onto `J₁` inside the tip ball
(uncountability from `FrontierPerfectGeneral` — no empty-interior hypothesis); the IFT branch
family (`SmoothPieceAssembly`) then eats the modulus-one supply of `PairComponentPropagation` and
the Baire pigeonhole fires.  What consumes the output: the smooth-piece rigidity endgame (P6),
the sole remaining epic of the both-connected lane.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.PairComponentPropagation
import GaloisForLFunctions.Bottcher.FrontierPerfectGeneral
import GaloisForLFunctions.Bottcher.SmoothPieceAssembly
import GaloisForLFunctions.Bottcher.RelativeMinimalRelation
import GaloisForLFunctions.Bottcher.RelativeFibreGeneric
import GaloisForLFunctions.Bottcher.BasinGlobalInverse
import GaloisForLFunctions.Bottcher.FilledJuliaConnected

open Polynomial Set Metric Bornology Filter Topology

namespace Bottcher

/-- **Relation ⟹ rel-open smooth Julia piece, at a hole-free tip.**  The conditional close of the
both-connected pigeonhole route: everything below is unconditional except the `HoleFreeTip` datum
(proven on paper for the class `−3/4 < c₂ < c₁ < 0`, collar epic pending) and the rigidity
consumer of the output. -/
theorem exists_relOpen_smooth_piece_of_holeFreeTip {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (h1M : c₁ ∈ mandelbrot) (h2M : c₂ ∈ mandelbrot)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    {z₀ : ℂ} {r : ℝ} (htip : HoleFreeTip c₁ c₂ z₀ r)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hpos : 1 ≤ (bivarPoly Q s).natDegree)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U) :
    ∃ (N : ℕ) (a : ℕ → ℂ → ℂ) (sT : Finset ℕ) (wfam : Fin N → ℂ → ℂ) (z₁ : ℂ) (ρ : ℝ)
      (k : Fin N) (Uop S : Set ℂ),
      sT ⊆ Finset.range (N + 1) ∧ N ∈ sT ∧ 1 ≤ N ∧ 0 < ρ ∧
      (∀ i ∈ sT, AnalyticOnNhd ℂ (a i) (filledJulia c₂)ᶜ) ∧
      a N z₁ ≠ 0 ∧ (fibrePoly a sT z₁).Separable ∧
      (∀ k', ContinuousOn (wfam k') (Metric.ball z₁ ρ)) ∧
      (∀ z ∈ Metric.ball z₁ ρ, ∀ k' l, k' ≠ l → wfam k' z ≠ wfam l z) ∧
      (∀ z ∈ Metric.ball z₁ ρ, (fibrePoly a sT z).natDegree = N) ∧
      (∀ k', ∀ z ∈ Metric.ball z₁ ρ, ∑ i ∈ sT, a i z * (wfam k' z) ^ i = 0) ∧
      z₁ ∈ frontier (filledJulia c₁) ∧
      IsClosed S ∧ S.Nonempty ∧ S ⊆ frontier (filledJulia c₁) ∧ S ⊆ Metric.ball z₁ ρ ∧
      S ⊆ (filledJulia c₂)ᶜ ∧
      IsOpen Uop ∧ (Uop ∩ S).Nonempty ∧ ∀ x ∈ Uop ∩ S, ‖wfam k x‖ = 1 := by
  classical
  -- global basin branches for both connected parameters
  obtain ⟨β₁, _ψ₁, hβ₁an, hβ₁esc, hβ₁mod, _, _, _, _, _, _⟩ :=
    exists_global_branch_with_inverse_of_mem_mandelbrot c₁ h1M
  obtain ⟨β₂, _ψ₂, hβ₂an, hβ₂esc, _, _, _, _, _, _, _⟩ :=
    exists_global_branch_with_inverse_of_mem_mandelbrot c₂ h2M
  -- the minimal separable relation with its far-field witness
  obtain ⟨T', wfar, hdeg', hwU, hwΩ₂, hlead_bc, hsep_bc, hEqOn'⟩ :=
    exists_separable_relation_of_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG Q s hpos hEqOn
  set N := T'.natDegree with hNdef
  set a : ℕ → ℂ → ℂ :=
    fun i z => (T'.coeff i).eval₂ (Polynomial.evalRingHom z) (β₂ z) with hadef
  have haeval : ∀ i x, a i x = (T'.coeff i).eval₂ (Polynomial.evalRingHom x) (β₂ x) :=
    fun i x => by rw [hadef]
  -- the witness data transfers from `bottcherCoord c₂` to `β₂` (they agree on `U`)
  have hcoeff_far : ∀ i, a i wfar
      = (T'.coeff i).eval₂ (Polynomial.evalRingHom wfar) (bottcherCoord c₂ wfar) := by
    intro i
    rw [haeval, hβ₂esc wfar (hU₂ hwU)]
  have hlead : a N wfar ≠ 0 := by rw [hcoeff_far]; exact hlead_bc
  have hsep : (fibrePoly a T'.support wfar).Separable := by
    have heq : fibrePoly a T'.support wfar
        = fibrePoly (fun i z => (T'.coeff i).eval₂ (Polynomial.evalRingHom z)
            (bottcherCoord c₂ z)) T'.support wfar := by
      unfold fibrePoly
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoeff_far]
    rw [heq]
    exact hsep_bc
  -- coefficient family analytic on the whole `c₂`-basin
  have haan : ∀ i ∈ T'.support, AnalyticOnNhd ℂ (a i) (filledJulia c₂)ᶜ := by
    intro i _
    have h := analyticOnNhd_eval₂_of_analyticOnNhd hβ₂an (T'.coeff i)
    intro z hz
    have := h z hz
    rw [hadef]
    exact this
  -- support bookkeeping
  have hT'ne : T' ≠ 0 := by
    intro h
    have h0 : N = 0 := by rw [hNdef, h, Polynomial.natDegree_zero]
    omega
  have hN : N ∈ T'.support := Polynomial.natDegree_mem_support_of_nonzero hT'ne
  have hsupp : T'.support ⊆ Finset.range (N + 1) :=
    Polynomial.supp_subset_range_natDegree_succ
  -- move the witness onto the Julia frontier inside the tip ball (countable avoidance)
  have h1conn : IsPreconnected (filledJulia c₁) := isPreconnected_filledJulia h1M
  have hz₀J : z₀ ∈ frontier (filledJulia c₁) := htip.2.1
  have hSΩ : Metric.ball z₀ r ∩ frontier (filledJulia c₁) ⊆ (filledJulia c₂)ᶜ := by
    rintro x ⟨hx1, _⟩ hxK₂
    have hmem : x ∈ Metric.ball z₀ r ∩ filledJulia c₂ := ⟨hx1, hxK₂⟩
    rw [htip.2.2.1] at hmem
    exact hmem
  have havoid : ∀ T : Set ℂ, T.Countable →
      ∃ z₁ ∈ Metric.ball z₀ r ∩ frontier (filledJulia c₁),
        z₁ ∈ (filledJulia c₂)ᶜ ∧ z₁ ∉ T := by
    apply countableAvoidance_of_uncountable_inter
    rw [Set.inter_eq_self_of_subset_left hSΩ]
    exact not_countable_ball_inter_frontier_filledJulia_of_preconnected h1conn hz₀J htip.1
  obtain ⟨z₁, hz₁S, hlead₁, hsep₁⟩ :=
    exists_sparse_fibre_separable_countableAvoidance hdeg' hsupp hN
      (isPreconnected_compl_filledJulia c₂) haan hwΩ₂ hlead hsep havoid
  -- the IFT branch family at the moved witness
  have haC : ∀ i ∈ T'.support, ContDiffAt ℂ ⊤ (a i) z₁ := fun i hi =>
    ((haan i hi) z₁ (hSΩ hz₁S)).contDiffAt
  obtain ⟨ρ, wfam, hρ, hwc, hwsep, hwdeg, hwrel, hspine⟩ :=
    exists_relOpen_smooth_piece_of_separable_witness hsupp hN hdeg' haC hlead₁ hsep₁
  -- the closed Julia piece inside both the branch ball and the tip ball
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z₁ hz₁S.1
  set ρ' : ℝ := min (ρ / 2) (ρ₁ / 2) with hρ'def
  have hρ' : 0 < ρ' := lt_min (by linarith) (by linarith)
  set S : Set ℂ := frontier (filledJulia c₁) ∩ Metric.closedBall z₁ ρ' with hSdef
  have hScl : IsClosed S := isClosed_frontier.inter Metric.isClosed_closedBall
  have hSne : S.Nonempty := ⟨z₁, hz₁S.2, Metric.mem_closedBall_self hρ'.le⟩
  have hSJ : S ⊆ frontier (filledJulia c₁) := fun x hx => hx.1
  have hSball : S ⊆ Metric.ball z₁ ρ := by
    intro x hx
    have h1 := Metric.mem_closedBall.mp hx.2
    have h2 : ρ' ≤ ρ / 2 := min_le_left _ _
    rw [Metric.mem_ball]
    linarith
  have hStip : S ⊆ Metric.ball z₀ r := by
    intro x hx
    apply hρ₁sub
    have h1 := Metric.mem_closedBall.mp hx.2
    have h2 : ρ' ≤ ρ₁ / 2 := min_le_right _ _
    rw [Metric.mem_ball]
    linarith
  -- the modulus-one supply on the Julia piece
  have hsupply : ∀ x ∈ S, ∃ y : ℂ, ‖y‖ = 1 ∧ (fibrePoly a T'.support x).IsRoot y := by
    intro x hx
    obtain ⟨y, hy1, hy2⟩ := holeFreeTip_modulus_one_supply hβ₁an hβ₁esc hβ₁mod hβ₂an hβ₂esc
      hUo hUne hU₁ hU₂ (fun i => T'.coeff i) T'.support hEqOn' htip (hSJ hx) (hStip hx)
    refine ⟨y, hy1, ?_⟩
    rw [Polynomial.IsRoot, eval_fibrePoly]
    calc ∑ i ∈ T'.support, a i x * y ^ i
        = ∑ i ∈ T'.support,
            ((T'.coeff i).eval₂ (Polynomial.evalRingHom x) (β₂ x)) * y ^ i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [haeval]
      _ = 0 := hy2
  have hSK₂ : S ⊆ (filledJulia c₂)ᶜ := fun x hx => hSΩ ⟨hStip hx, hSJ hx⟩
  -- the Baire pigeonhole fires
  obtain ⟨k, Uop, hUop, hUopne, hmod1⟩ := hspine S hScl hSne hSball hsupply
  exact ⟨N, a, T'.support, wfam, z₁, ρ, k, Uop, S, hsupp, hN, hdeg', hρ, haan, hlead₁,
    hsep₁, hwc, hwsep, hwdeg, hwrel, hz₁S.2, hScl, hSne, hSJ, hSball, hSK₂,
    hUop, hUopne, hmod1⟩

end Bottcher
