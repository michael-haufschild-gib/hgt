import Mathlib

/-!
# The Laguerre shift preserves real-rootedness

For a real polynomial `p` that splits over `ℝ` and a real `β`, the shift `p' − β·p` splits over `ℝ`
as well.  The exponential gauge `e^{−βx}p(x)` has the shift as its derivative, so Rolle's theorem
produces a root between every two consecutive roots of `p`, the multiplicities at the roots of `p`
themselves drop by exactly one, and — when `β ≠ 0`, where the shift keeps the degree — the decay of
the gauge at one end of the line supplies the last root.
-/

open Polynomial Filter Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Laguerre shift `p' − β·p`. -/
def laguerreShift (β : ℝ) (p : ℝ[X]) : ℝ[X] := derivative p - C β * p

@[simp] theorem eval_laguerreShift (β : ℝ) (p : ℝ[X]) (x : ℝ) :
    (laguerreShift β p).eval x = (derivative p).eval x - β * p.eval x := by
  simp [laguerreShift]

/-- The exponential gauge differentiates to the Laguerre shift. -/
theorem hasDerivAt_expGauge (β : ℝ) (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(β * y)) * p.eval y)
      (Real.exp (-(β * x)) * (laguerreShift β p).eval x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(β * y)) (-β) x := by
    have h := (hasDerivAt_id x).const_mul (-β)
    simpa [neg_mul] using h
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(β * y))) (Real.exp (-(β * x)) * (-β)) x := by
    simpa using h1.exp
  have h3 : HasDerivAt (fun y : ℝ => p.eval y) ((derivative p).eval x) x := p.hasDerivAt x
  have hmul := h2.mul h3
  rw [show ((fun y : ℝ => Real.exp (-(β * y))) * fun y : ℝ => p.eval y)
      = fun y : ℝ => Real.exp (-(β * y)) * p.eval y from rfl] at hmul
  refine hmul.congr_deriv ?_
  rw [eval_laguerreShift]
  ring

theorem eval_laguerreShift_eq_zero_of_deriv {β : ℝ} {p : ℝ[X]} {c : ℝ}
    (h : deriv (fun y : ℝ => Real.exp (-(β * y)) * p.eval y) c = 0) :
    (laguerreShift β p).eval c = 0 := by
  have hd := (hasDerivAt_expGauge β p c).deriv
  rw [h] at hd
  rcases mul_eq_zero.1 hd.symm with h0 | h0
  · exact absurd h0 (Real.exp_ne_zero _)
  · exact h0

theorem continuous_expGauge (β : ℝ) (p : ℝ[X]) :
    Continuous (fun y : ℝ => Real.exp (-(β * y)) * p.eval y) := by
  fun_prop

/-- Between two points where the gauge vanishes there is a root of the shift. -/
theorem exists_root_laguerreShift_of_lt {β : ℝ} {p : ℝ[X]} {u v : ℝ} (huv : u < v)
    (hu : p.eval u = 0) (hv : p.eval v = 0) :
    ∃ c ∈ Ioo u v, (laguerreShift β p).eval c = 0 := by
  obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_zero huv
    (continuous_expGauge β p).continuousOn (by rw [hu, hv]; ring)
  exact ⟨c, hc, eval_laguerreShift_eq_zero_of_deriv hderiv⟩

/-- The multiplicity of a root of `p` in the shift drops by at most one. -/
theorem le_rootMultiplicity_laguerreShift {β : ℝ} {p : ℝ[X]} (hp : p ≠ 0)
    (hq : laguerreShift β p ≠ 0) (x : ℝ) :
    rootMultiplicity x p - 1 ≤ rootMultiplicity x (laguerreShift β p) := by
  classical
  set m : ℕ := rootMultiplicity x p with hm
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  rw [le_rootMultiplicity_iff hq]
  have hdvd_p : ((X - C x) ^ (m - 1) : ℝ[X]) ∣ p := by
    refine dvd_trans (pow_dvd_pow _ (by omega)) (pow_rootMultiplicity_dvd p x)
  have hroot : p.IsRoot x := by
    rw [← rootMultiplicity_pos hp]
    omega
  have hdvd_d : ((X - C x) ^ (m - 1) : ℝ[X]) ∣ derivative p := by
    have hd0 : derivative p ≠ 0 := by
      intro h0
      have hdeg : p.natDegree = 0 := Polynomial.derivative_eq_zero.1 h0
      have hpc := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      rw [hpc] at hroot
      rw [Polynomial.IsRoot, Polynomial.eval_C] at hroot
      exact hp (by rw [hpc, hroot, map_zero])
    rw [← le_rootMultiplicity_iff hd0, derivative_rootMultiplicity_of_root hroot]
  exact dvd_sub hdvd_d (Dvd.dvd.mul_left hdvd_p _)

/-! ### A real polynomial never misses exactly one root -/

/-- Over `ℝ` the number of roots and the degree cannot differ by exactly one: the missing factor
would be linear, hence would have a real root. -/
theorem natDegree_ne_card_roots_succ {q : ℝ[X]} (hq : q ≠ 0) :
    q.natDegree ≠ q.roots.card + 1 := by
  classical
  intro hcard
  obtain ⟨g, hg⟩ := prod_multiset_X_sub_C_dvd q
  have hRdeg : (Multiset.map (fun a : ℝ => X - C a) q.roots).prod.natDegree = q.roots.card :=
    natDegree_multiset_prod_X_sub_C_eq_card _
  have hR0 : (Multiset.map (fun a : ℝ => X - C a) q.roots).prod ≠ 0 := by
    intro h0
    exact hq (by rw [hg, h0, zero_mul])
  have hg0 : g ≠ 0 := by
    intro h0
    exact hq (by rw [hg, h0, mul_zero])
  have hdeg : q.natDegree
      = (Multiset.map (fun a : ℝ => X - C a) q.roots).prod.natDegree + g.natDegree := by
    conv_lhs => rw [hg]
    exact natDegree_mul hR0 hg0
  have hgdeg : g.natDegree = 1 := by omega
  have hgsplit : g.Splits := Polynomial.Splits.of_natDegree_le_one (by omega)
  have hgroots : g.roots.card = 1 := by
    rw [splits_iff_card_roots] at hgsplit
    omega
  obtain ⟨r, hr⟩ : ∃ r, r ∈ g.roots := by
    rw [← Multiset.card_pos_iff_exists_mem, hgroots]
    norm_num
  have hgr : (X - C r : ℝ[X]) ∣ g := dvd_iff_isRoot.2 ((mem_roots hg0).1 hr)
  have hcR : ((X - C r) ^ (Multiset.count r q.roots) : ℝ[X])
      ∣ (Multiset.map (fun a : ℝ => X - C a) q.roots).prod := by
    have hle : Multiset.replicate (Multiset.count r q.roots) r ≤ q.roots :=
      Multiset.le_count_iff_replicate_le.1 (le_refl _)
    have hmap : Multiset.map (fun a : ℝ => X - C a)
        (Multiset.replicate (Multiset.count r q.roots) r)
        = Multiset.replicate (Multiset.count r q.roots) (X - C r : ℝ[X]) :=
      Multiset.map_replicate _ _ _
    have hdd := Multiset.prod_dvd_prod_of_le
      (Multiset.map_le_map hle (f := fun a : ℝ => X - C a))
    rw [hmap, Multiset.prod_replicate] at hdd
    exact hdd
  have hcq : ((X - C r) ^ (Multiset.count r q.roots + 1) : ℝ[X]) ∣ q := by
    have hmm := mul_dvd_mul hcR hgr
    rw [← pow_succ] at hmm
    nth_rewrite 2 [hg]
    exact hmm
  have hle2 : Multiset.count r q.roots + 1 ≤ rootMultiplicity r q :=
    (le_rootMultiplicity_iff hq).2 hcq
  rw [← count_roots] at hle2
  omega

/-! ### The main theorem -/

theorem laguerreShift_ne_zero {β : ℝ} {p : ℝ[X]} (hn : 1 ≤ p.natDegree) :
    laguerreShift β p ≠ 0 := by
  intro h0
  have hderiv : derivative p = C β * p := by
    have := h0
    rw [laguerreShift, sub_eq_zero] at this
    exact this
  have hdlt : (derivative p).natDegree < p.natDegree := natDegree_derivative_lt (by omega)
  rcases eq_or_ne β 0 with rfl | hβ
  · rw [map_zero, zero_mul] at hderiv
    have := Polynomial.derivative_eq_zero.1 hderiv
    omega
  · have : (C β * p).natDegree = p.natDegree := by
      rw [natDegree_C_mul (by simpa using hβ)]
    rw [hderiv, this] at hdlt
    omega


/-- The distinct roots of `p` interleave with the roots of the shift. -/
theorem card_roots_toFinset_le_laguerreShift_sdiff_succ (β : ℝ) (p : ℝ[X]) :
    p.roots.toFinset.card
      ≤ ((laguerreShift β p).roots.toFinset \ p.roots.toFinset).card + 1 := by
  classical
  rcases eq_or_ne (laguerreShift β p) 0 with hq | hq
  · have hdeg : p.natDegree = 0 := by
      by_contra h
      exact laguerreShift_ne_zero (β := β) (p := p) (by omega) hq
    have h1 : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    have h2 := p.card_roots'
    omega
  have hp : p ≠ 0 := by
    intro h0
    exact hq (by rw [h0]; simp [laguerreShift])
  refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy _ => ?_
  rw [Multiset.mem_toFinset, mem_roots hp] at hx hy
  obtain ⟨z, hz1, hz2⟩ := exists_root_laguerreShift_of_lt (β := β) hxy hx hy
  refine ⟨z, ?_, hz1.1, hz1.2⟩
  rw [Multiset.mem_toFinset, mem_roots hq]
  exact hz2

/-- Counted with multiplicity, the shift loses at most one root. -/
theorem card_roots_le_laguerreShift (β : ℝ) (p : ℝ[X]) :
    Multiset.card p.roots ≤ Multiset.card (laguerreShift β p).roots + 1 := by
  classical
  rcases eq_or_ne (laguerreShift β p) 0 with hq | hq
  · have hdeg : p.natDegree = 0 := by
      by_contra h
      exact laguerreShift_ne_zero (β := β) (p := p) (by omega) hq
    have h2 := p.card_roots'
    omega
  have hp : p ≠ 0 := by
    intro h0
    exact hq (by rw [h0]; simp [laguerreShift])
  calc
    Multiset.card p.roots = ∑ x ∈ p.roots.toFinset, p.roots.count x :=
      (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ p.roots.toFinset, (p.roots.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
        Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx)
    _ = (∑ x ∈ p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ ≤ (∑ x ∈ p.roots.toFinset, (laguerreShift β p).rootMultiplicity x) +
          (((laguerreShift β p).roots.toFinset \ p.roots.toFinset).card + 1) :=
      add_le_add
        (Finset.sum_le_sum fun _ _ => le_rootMultiplicity_laguerreShift hp hq _)
        (card_roots_toFinset_le_laguerreShift_sdiff_succ β p)
    _ ≤ (∑ x ∈ p.roots.toFinset, (laguerreShift β p).roots.count x) +
          ((∑ x ∈ (laguerreShift β p).roots.toFinset \ p.roots.toFinset,
            (laguerreShift β p).roots.count x) + 1) := by
      simp only [← count_roots, Finset.card_eq_sum_ones]
      gcongr with x hx
      rw [Nat.succ_le_iff, Multiset.count_pos, ← Multiset.mem_toFinset]
      exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card (laguerreShift β p).roots + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union, ← Multiset.toFinset_sum_count_eq,
        ← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx₂
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

theorem natDegree_laguerreShift_le (β : ℝ) (p : ℝ[X]) :
    (laguerreShift β p).natDegree ≤ p.natDegree := by
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans (natDegree_derivative_le p) (Nat.sub_le _ _)
  · exact natDegree_C_mul_le β p

/-- **The Laguerre shift preserves real-rootedness.** -/
theorem splits_laguerreShift {p : ℝ[X]} (hp : p.Splits) (β : ℝ) :
    (laguerreShift β p).Splits := by
  classical
  rcases eq_or_ne (laguerreShift β p) 0 with hq | hq
  · rw [hq]
    exact Polynomial.Splits.of_natDegree_le_one (by simp)
  rw [splits_iff_card_roots] at hp ⊢
  have hupper : Multiset.card (laguerreShift β p).roots ≤ (laguerreShift β p).natDegree :=
    card_roots' _
  have hlower := card_roots_le_laguerreShift β p
  have hdq := natDegree_laguerreShift_le β p
  have hne := natDegree_ne_card_roots_succ hq
  omega

end

end GaloisForLFunctions.HTGeometry
