/-
# Disk-side branch-exhaustion continuation (the Fatou-free supplier)

The disk analogue of the U0 program's `continues_of_separable_relation`: if the disk model `h`
(analytic on the unit disk) satisfies a polynomial relation `P(t, h t) = 0` on the disk and at a
circle point `ζ₀` the fibre `P(ζ₀,·)` is separable with surviving leading coefficient, then `h`
continues analytically across `ζ₀` — with **no boundary-limit (Fatou) input**. The `d` simple fibre
roots give `d` analytic implicit-function branches; at each disk point near `ζ₀` the fibre polynomial
has exactly `d` roots, so `h` must equal one of the `d` separated branch values (`root_complete`);
`branch_selection` on the convex lens `ball 0 1 ∩ ball ζ₀ ρ` pins `h` to a single branch — the
continuation. This is the engine that turns "minimal relation" into "continuation across a whole
boundary arc", contradicting `natural_boundary_of_even_fe`.
-/
import GaloisForLFunctions.U0.HolomorphicIFT
import GaloisForLFunctions.Bottcher.ArcContinuation
open Polynomial Filter Topology Metric Complex Set HolomorphicIFT
namespace Bottcher
noncomputable section

/-- **Separable fibre ⟹ continuation across the circle point (disk version, Fatou-free).**
Branch exhaustion (`root_complete`) + locally-constant selection (`branch_selection`) on the convex
lens replace any boundary-limit hypothesis. -/
theorem continuesAcross_of_separable_fibre_disk {h : ℂ → ℂ}
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (P : (Polynomial ℂ)[X]) (ζ₀ : ℂ) (hζ₀ : ‖ζ₀‖ = 1)
    (hlead : P.leadingCoeff.eval ζ₀ ≠ 0)
    (hsep : (P.map (evalRingHom ζ₀)).Separable)
    (hdeg : 1 ≤ P.natDegree)
    (hrel : ∀ t ∈ ball (0:ℂ) 1, P.eval₂ (evalRingHom t) (h t) = 0) :
    ContinuesAcross h ζ₀ := by
  classical
  set f : ℂ × ℂ → ℂ := fun q => P.eval₂ (evalRingHom q.1) q.2 with hf
  set ψ := evalRingHom ζ₀ with hψ
  set d := P.natDegree with hd
  have hfval : ∀ z w : ℂ, f (z, w) = (P.map (evalRingHom z)).eval w := by
    intro z w; simp only [hf]; rw [eval_map]
  have hsimple : ∀ x : ℂ, (P.map ψ).eval x = 0 → (derivative (P.map ψ)).eval x ≠ 0 := by
    intro x hx hdx
    obtain ⟨u, v, huv⟩ := hsep
    have key := congrArg (Polynomial.eval x) huv
    simp only [eval_add, eval_mul, hx, hdx, mul_zero, eval_one, add_zero] at key
    exact one_ne_zero key.symm
  have hdeg_Pz : (P.map ψ).natDegree = d := natDegree_map_of_leadingCoeff_ne_zero ψ hlead
  have hPz_ne : (P.map ψ) ≠ 0 := by intro h'; rw [h', natDegree_zero] at hdeg_Pz; omega
  have hnodup : (P.map ψ).roots.Nodup := nodup_roots hsep
  have hcard : (P.map ψ).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup hnodup, IsAlgClosed.card_roots_eq_natDegree, hdeg_Pz]
  set s := (P.map ψ).roots.toFinset with hs
  set a : Fin d → ℂ := fun i => (s.equivFin.symm (finCongr hcard.symm i) : ℂ) with ha
  have hainj : Function.Injective a := by
    intro i j hij
    apply (finCongr hcard.symm).injective
    apply s.equivFin.symm.injective
    exact Subtype.ext hij
  have haroot : ∀ i, (P.map ψ).eval (a i) = 0 := by
    intro i
    have hmem : a i ∈ (P.map ψ).roots :=
      Multiset.mem_toFinset.mp (s.equivFin.symm (finCongr hcard.symm i)).2
    exact isRoot_of_mem_roots hmem
  have hbranch : ∀ i, ∃ r : ℂ → ℂ, AnalyticAt ℂ r ζ₀ ∧ r ζ₀ = a i ∧
      ∀ᶠ z in 𝓝 ζ₀, f (z, r z) = 0 := by
    intro i
    have hf_an : AnalyticAt ℂ f (ζ₀, a i) := bivar_analytic P (ζ₀, a i)
    have h0 : f (ζ₀, a i) = 0 := by rw [hfval]; exact haroot i
    have hfw : (fderiv ℂ f (ζ₀, a i)) (0, 1) ≠ 0 := by
      rw [hf, partial_w_deriv P ζ₀ (a i), ← Polynomial.derivative_map]
      exact hsimple (a i) (haroot i)
    exact holo_implicit hf_an h0 hfw
  choose r hr_an hr0 hr_rel using hbranch
  have E1 : ∀ᶠ z in 𝓝 ζ₀, ∀ i, f (z, r i z) = 0 := eventually_all.mpr hr_rel
  have E2 : ∀ᶠ z in 𝓝 ζ₀, ∀ i j, i ≠ j → r i z ≠ r j z := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun z h' => (h' hij).elim)
    · have hne : r i ζ₀ ≠ r j ζ₀ := by rw [hr0, hr0]; exact fun h' => hij (hainj h')
      have hcij : ContinuousAt (fun z => r i z - r j z) ζ₀ :=
        ((hr_an i).continuousAt).sub ((hr_an j).continuousAt)
      have hev := hcij.eventually_ne (sub_ne_zero.mpr hne)
      filter_upwards [hev] with z hz; exact fun _ => sub_ne_zero.mp hz
  have E3 : ∀ᶠ z in 𝓝 ζ₀, P.leadingCoeff.eval z ≠ 0 :=
    (Polynomial.continuous P.leadingCoeff).continuousAt.eventually_ne hlead
  have E4 : ∀ᶠ z in 𝓝 ζ₀, ∀ i, AnalyticAt ℂ (r i) z := by
    rw [eventually_all]; intro i
    exact (hr_an i).eventually_analyticAt
  have hcombo := (E1.and (E2.and (E3.and E4)))
  rw [Metric.eventually_nhds_iff] at hcombo
  obtain ⟨ρ₀, hρ₀, hball⟩ := hcombo
  set ρ := min ρ₀ (1/2) with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ (by norm_num)
  set U : Set ℂ := ball (0:ℂ) 1 ∩ ball ζ₀ ρ with hU
  have hUsub : ∀ z ∈ U, dist z ζ₀ < ρ₀ :=
    fun z hz => lt_of_lt_of_le (mem_ball.mp hz.2) (min_le_left _ _)
  have hpre : IsPreconnected U := ((convex_ball (0:ℂ) 1).inter (convex_ball ζ₀ ρ)).isPreconnected
  have hρ2 : ρ ≤ 1/2 := min_le_right _ _
  have hUne : U.Nonempty := by
    refine ⟨((1 - ρ/2 : ℝ) : ℂ) * ζ₀, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, hζ₀, mul_one,
        abs_of_pos (by linarith)]
      linarith
    · rw [mem_ball, dist_eq_norm]
      have heq : ((1 - ρ/2 : ℝ) : ℂ) * ζ₀ - ζ₀ = ((-(ρ/2) : ℝ) : ℂ) * ζ₀ := by
        push_cast; ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, hζ₀, mul_one,
        abs_of_neg (by linarith), neg_neg]
      linarith
  have hh : ContinuousOn h U := hhd.continuousOn.mono (Set.inter_subset_left)
  have hr_cont : ∀ i, ContinuousOn (r i) U :=
    fun i z hz => ((hball (hUsub z hz)).2.2.2 i).continuousAt.continuousWithinAt
  have hsep_branch : ∀ z ∈ U, ∀ i j, i ≠ j → r i z ≠ r j z :=
    fun z hz => (hball (hUsub z hz)).2.1
  have hmem : ∀ z ∈ U, ∃ i, h z = r i z := by
    intro z hz
    set Q := P.map (evalRingHom z) with hQ
    have hlz : P.leadingCoeff.eval z ≠ 0 := (hball (hUsub z hz)).2.2.1
    have hQdeg : Q.natDegree = d := natDegree_map_of_leadingCoeff_ne_zero _ hlz
    have hQne : Q ≠ 0 := by intro h'; rw [h', natDegree_zero] at hQdeg; omega
    have ha' : Function.Injective (fun i => r i z) :=
      fun i j hij => by_contra fun hne => (hsep_branch z hz i j hne) hij
    have ha'root : ∀ i, Q.IsRoot (r i z) := by
      intro i
      have hh2 := (hball (hUsub z hz)).1 i
      rw [hfval] at hh2; exact hh2
    have hu0root : Q.IsRoot (h z) := by
      have hh3 := hrel z hz.1; rw [← eval_map] at hh3; exact hh3
    exact root_complete hQne hQdeg ha' ha'root hu0root
  obtain ⟨j, hj⟩ := branch_selection hpre hUne hh hr_cont hsep_branch hmem
  -- package as the 2-arg ContinuesAcross
  refine ⟨ball ζ₀ ρ, isOpen_ball, mem_ball_self hρ, r j, ?_, ?_⟩
  · intro z hz
    exact ((hball (lt_of_lt_of_le (mem_ball.mp hz) (min_le_left _ _))).2.2.2 j).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hj z ⟨hz.2, hz.1⟩).symm

end
end Bottcher
