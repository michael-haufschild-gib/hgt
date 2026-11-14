import GaloisForLFunctions.GaloisTheoryOfZeros.TheReflectionIsTheOnlySymmetryOfTheHeatCoverOverTheForwardTimes
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The heat cover over the forward times is connected and has no polynomial factor

* **Connected** (`isConnected_forwardCover`). The set of the points `(τ, z)` with `H_τ(z) = 0`
  over the forward times off the branch times is connected: the cover is irreducible as a space.
* **No polynomial factor** (`exists_isRoot_complexHeat_ne_zero`). Let `P_τ` be a monic polynomial
  of a fixed degree `n ≥ 1` whose coefficients are continuous functions of the forward time off
  the branch times. Then some root of some `P_τ` is not a zero of `H_τ`. So no zero of the
  family satisfies an equation of finite degree with single-valued continuous coefficients all of
  whose roots are zeros: every zero has infinite degree over the functions of the time.

Proof. Let `S` be a subset of the cover that is open and closed in it
(`forall_mem_or_forall_notMem_forwardCover`). The map `z` on `S`, `−z` off `S` is a continuous
map of the cover that carries zeros to zeros, so it is `z` everywhere or `−z` everywhere, and no
zero is `0`: `S` is everything or nothing. For a polynomial family take the points of the cover
that are roots. This set is closed in the cover by continuity of the value. It is open: near a
root `z₀` of `P_τ₀` the monic polynomial `P_τ` has a root within `|P_τ(z₀)|^{1/n}` of `z₀`
(`exists_isRoot_norm_sub_lt`), this root is a zero of `H_τ`, and the simple zero through
`(τ₀, z₀)` is the only zero nearby. A fibre is infinite and a polynomial has finitely many roots.
-/

open Complex Set Metric Filter Topology Polynomial
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-! ## Open and closed subsets of the cover -/

/-- No zero of `H_τ` over a forward time off the branch times is at the centre. -/
theorem snd_ne_zero_of_mem_forwardCover {x : ℂ × ℂ} (hx : x ∈ forwardCover) : x.2 ≠ 0 := by
  intro h
  have h0 := hx.2.2
  rw [h] at h0
  exact hx.2.1 (mem_branchTimes_of_complexHeat_center_eq_zero h0)

/-- **A subset of the forward cover that is open and closed in it is everything or nothing.** -/
theorem forall_mem_or_forall_notMem_forwardCover {S : Set (ℂ × ℂ)}
    (hopen : ∀ x ∈ forwardCover, x ∈ S → ∀ᶠ y in 𝓝[forwardCover] x, y ∈ S)
    (hclosed : ∀ x ∈ forwardCover, x ∉ S → ∀ᶠ y in 𝓝[forwardCover] x, y ∉ S) :
    (∀ x ∈ forwardCover, x ∈ S) ∨ ∀ x ∈ forwardCover, x ∉ S := by
  classical
  -- the map `z` on `S`, `−z` off `S` is a deck map
  have hf : ContinuousOn (fun x : ℂ × ℂ => if x ∈ S then x.2 else -x.2) forwardCover := by
    intro x hx
    by_cases hxS : x ∈ S
    · refine continuous_snd.continuousWithinAt.congr_of_eventuallyEq
        ((hopen x hx hxS).mono fun y hy => ?_) ?_
      · exact if_pos hy
      · exact if_pos hxS
    · refine continuous_snd.neg.continuousWithinAt.congr_of_eventuallyEq
        ((hclosed x hx hxS).mono fun y hy => ?_) ?_
      · exact if_neg hy
      · exact if_neg hxS
  have hzero : ∀ x ∈ forwardCover, complexHeat x.1 (if x ∈ S then x.2 else -x.2) = 0 := by
    intro x hx
    by_cases hxS : x ∈ S
    · rw [if_pos hxS]
      exact hx.2.2
    · rw [if_neg hxS, complexHeat_neg]
      exact hx.2.2
  rcases eq_snd_or_eq_neg_snd_of_continuousOn_forwardCover hf hzero with h | h
  · refine Or.inl fun x hx => ?_
    by_contra hxS
    have e : -x.2 = x.2 := (if_neg hxS).symm.trans (h x hx)
    have h2 : (2 : ℂ) * x.2 = 0 := by linear_combination -e
    exact snd_ne_zero_of_mem_forwardCover hx ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
  · refine Or.inr fun x hx hxS => ?_
    have e : x.2 = -x.2 := (if_pos hxS).symm.trans (h x hx)
    have h2 : (2 : ℂ) * x.2 = 0 := by linear_combination e
    exact snd_ne_zero_of_mem_forwardCover hx ((mul_eq_zero.mp h2).resolve_left two_ne_zero)

theorem isPreconnected_forwardCover : IsPreconnected forwardCover := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv hdisj
  rcases forall_mem_or_forall_notMem_forwardCover (S := u)
    (fun x _ hxu => mem_nhdsWithin_of_mem_nhds (hu.mem_nhds hxu))
    (fun x hx hxu => by
      have hxv : x ∈ v := (huv hx).resolve_left hxu
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hv.mem_nhds hxv), self_mem_nhdsWithin]
        with y hy hys
      intro hyu
      have hmem : y ∈ forwardCover ∩ (u ∩ v) := ⟨hys, hyu, hy⟩
      rw [hdisj] at hmem
      exact hmem) with h | h
  · exact Or.inl h
  · exact Or.inr fun x hx => (huv hx).resolve_left (h x hx)

private theorem eighth_forward : 0 < (((1 / 8 : ℝ) : ℂ)).re ∧ ((1 / 8 : ℝ) : ℂ) ∉ branchTimes :=
  ⟨by rw [Complex.ofReal_re]; norm_num, ofReal_not_mem_branchTimes_of_eighth_le le_rfl⟩

/-- **The heat cover over the forward times off the branch times is connected.** -/
theorem isConnected_forwardCover : IsConnected forwardCover := by
  haveI := infinite_fibre eighth_forward.1 eighth_forward.2
  obtain ⟨p⟩ := (inferInstance : Nonempty {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0})
  exact ⟨⟨(((1 / 8 : ℝ) : ℂ), p.1), eighth_forward.1, eighth_forward.2, p.2⟩,
    isPreconnected_forwardCover⟩

/-! ## No polynomial factor -/

/-- A monic polynomial of degree `n` has a root within `ε` of every place where its value is
below `εⁿ`. -/
theorem exists_isRoot_norm_sub_lt {p : ℂ[X]} (hp : p.Monic) {z : ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ‖p.eval z‖ < ε ^ p.natDegree) : ∃ r, p.IsRoot r ∧ ‖z - r‖ < ε := by
  by_contra hcon
  have hall : ∀ r ∈ p.roots, ε ≤ ‖z - r‖ := fun r hr =>
    not_lt.mp fun hlt => hcon ⟨r, (mem_roots'.mp hr).2, hlt⟩
  have hnorm : ‖p.eval z‖ = (p.roots.map fun r => ‖z - r‖).prod := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp z]
    exact (map_multiset_prod (normHom : ℂ →*₀ ℝ) _).trans (by rw [Multiset.map_map]; rfl)
  have hge : ε ^ p.natDegree ≤ ‖p.eval z‖ := by
    rw [hnorm, ← IsAlgClosed.card_roots_eq_natDegree (p := p), ← Multiset.prod_replicate,
      ← Multiset.map_const']
    exact Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ => hε.le) hall
  exact absurd h (not_lt.mpr hge)

/-- **The heat family has no polynomial factor over the forward times.** Let `P_τ` be monic of
degree `n ≥ 1` with coefficients continuous on the forward times off the branch times. Then for
some such time a root of `P_τ` is not a zero of `H_τ`. -/
theorem exists_isRoot_complexHeat_ne_zero {P : ℂ → ℂ[X]} {n : ℕ} (hn : 0 < n)
    (hmonic : ∀ τ : ℂ, 0 < τ.re → τ ∉ branchTimes → (P τ).Monic)
    (hdeg : ∀ τ : ℂ, 0 < τ.re → τ ∉ branchTimes → (P τ).natDegree = n)
    (hcont : ∀ k, ContinuousOn (fun τ => (P τ).coeff k) {τ : ℂ | 0 < τ.re ∧ τ ∉ branchTimes}) :
    ∃ τ z : ℂ, 0 < τ.re ∧ τ ∉ branchTimes ∧ (P τ).IsRoot z ∧ complexHeat τ z ≠ 0 := by
  by_contra hcon
  have hroot : ∀ τ z : ℂ, 0 < τ.re → τ ∉ branchTimes → (P τ).IsRoot z →
      complexHeat τ z = 0 := by
    intro τ z hτ hb hr
    by_contra h
    exact hcon ⟨τ, z, hτ, hb, hr, h⟩
  -- the value of the polynomial at a continuous place is continuous on the cover
  have hEval : ∀ g : ℂ × ℂ → ℂ, ContinuousOn g forwardCover →
      ContinuousOn (fun x : ℂ × ℂ => (P x.1).eval (g x)) forwardCover := by
    intro g hg
    have hsum : ContinuousOn (fun x : ℂ × ℂ =>
        ∑ k ∈ Finset.range (n + 1), (P x.1).coeff k * g x ^ k) forwardCover :=
      continuousOn_finsetSum _ fun k _ =>
        ((hcont k).comp continuous_fst.continuousOn fun x hx => ⟨hx.1, hx.2.1⟩).mul (hg.pow k)
    refine hsum.congr fun x hx => ?_
    show (P x.1).eval (g x) = ∑ k ∈ Finset.range (n + 1), (P x.1).coeff k * g x ^ k
    rw [Polynomial.eval_eq_sum_range, hdeg x.1 hx.1 hx.2.1]
  have h8₀ := eighth_forward.1
  have h8 := eighth_forward.2
  -- open: a root of `P_τ` near `z₀` is the zero of the chart through `(τ₀, z₀)`
  have hopen : ∀ x ∈ forwardCover, x ∈ {x : ℂ × ℂ | (P x.1).eval x.2 = 0} →
      ∀ᶠ y in 𝓝[forwardCover] x, y ∈ {x : ℂ × ℂ | (P x.1).eval x.2 = 0} := by
    rintro ⟨τ₀, z₀⟩ hx hxS
    obtain ⟨W, hW, hτW, ρ, hρ, ζ, -, -, hchart⟩ := exists_simple_zero_chart hx.2.2
      (deriv_complexHeat_ne_zero_of_not_mem_branchTimes hx.2.1 hx.2.2)
    have hsmall : ∀ᶠ y in 𝓝[forwardCover] (τ₀, z₀), ‖(P y.1).eval z₀‖ < (ρ / 2) ^ n := by
      have hc := (hEval (fun _ => z₀) continuousOn_const (τ₀, z₀) hx).norm
      have h0 : ‖(P τ₀).eval z₀‖ < (ρ / 2) ^ n := by
        rw [show (P τ₀).eval z₀ = 0 from hxS, norm_zero]
        exact pow_pos (half_pos hρ) n
      exact hc.eventually (eventually_lt_nhds h0)
    have hnear : ∀ᶠ y in 𝓝[forwardCover] (τ₀, z₀), y.1 ∈ W ∧ y.2 ∈ ball z₀ (ρ / 2) :=
      mem_nhdsWithin_of_mem_nhds
        (prod_mem_nhds (hW.mem_nhds hτW) (ball_mem_nhds z₀ (half_pos hρ)))
    filter_upwards [hsmall, hnear, self_mem_nhdsWithin] with y hy1 hy2 hy
    obtain ⟨r, hr, hrz⟩ := exists_isRoot_norm_sub_lt (hmonic y.1 hy.1 hy.2.1) (half_pos hρ)
      (by rw [hdeg y.1 hy.1 hy.2.1]; exact hy1)
    have hρ' : ρ / 2 < ρ := half_lt_self hρ
    have hrb : r ∈ ball z₀ ρ := by
      rw [mem_ball, dist_comm, dist_eq_norm]
      exact hrz.trans hρ'
    have e1 := (hchart y.1 hy2.1).2.2.2 r hrb (hroot y.1 r hy.1 hy.2.1 hr)
    have e2 := (hchart y.1 hy2.1).2.2.2 y.2 (ball_subset_ball hρ'.le hy2.2) hy.2.2
    show (P y.1).eval y.2 = 0
    rw [e2, ← e1]
    exact hr
  -- closed: the value is continuous on the cover
  have hclosed : ∀ x ∈ forwardCover, x ∉ {x : ℂ × ℂ | (P x.1).eval x.2 = 0} →
      ∀ᶠ y in 𝓝[forwardCover] x, y ∉ {x : ℂ × ℂ | (P x.1).eval x.2 = 0} := fun x hx hxS =>
    Filter.Tendsto.eventually_ne (hEval (fun y => y.2) continuous_snd.continuousOn x hx) hxS
  rcases forall_mem_or_forall_notMem_forwardCover hopen hclosed with h | h
  · -- every zero over the time `1/8` is a root: infinitely many roots
    have hfin : {z : ℂ | (P ((1 / 8 : ℝ) : ℂ)).IsRoot z}.Finite :=
      Polynomial.finite_setOf_isRoot (hmonic _ h8₀ h8).ne_zero
    have hsub : {z : ℂ | complexHeat ((1 / 8 : ℝ) : ℂ) z = 0} ⊆
        {z : ℂ | (P ((1 / 8 : ℝ) : ℂ)).IsRoot z} := fun z hz =>
      h (((1 / 8 : ℝ) : ℂ), z) ⟨h8₀, h8, hz⟩
    haveI := infinite_fibre h8₀ h8
    haveI : Finite {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0} := (hfin.subset hsub).to_subtype
    exact not_finite {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}
  · -- no zero is a root, but the polynomial over the time `1/8` has a root
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (P ((1 / 8 : ℝ) : ℂ)) (by
      rw [Ne, Polynomial.degree_eq_natDegree (hmonic _ h8₀ h8).ne_zero, hdeg _ h8₀ h8]
      exact_mod_cast hn.ne')
    exact h (((1 / 8 : ℝ) : ℂ), r) ⟨h8₀, h8, hroot _ r h8₀ h8 hr⟩ hr

end GaloisForLFunctions.GaloisTheoryOfZeros
