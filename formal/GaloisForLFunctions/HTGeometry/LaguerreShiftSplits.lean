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
  set R : ℝ[X] := (Multiset.map (fun a => X - C a) q.roots).prod with hR
  have hRdeg : R.natDegree = q.roots.card := by
    rw [hR]
    exact natDegree_multiset_prod_X_sub_C_eq_card _
  obtain ⟨g, hg⟩ := prod_multiset_X_sub_C_dvd q
  have hR0 : R ≠ 0 := by
    intro h0
    rw [hR] at h0
    rw [hR, h0] at hRdeg
    simp at hRdeg
    exact hq (by rw [hg, hR, h0, zero_mul])
  have hg0 : g ≠ 0 := by
    intro h0
    exact hq (by rw [hg, h0, mul_zero])
  have hdeg : q.natDegree = R.natDegree + g.natDegree := by
    rw [hg, natDegree_mul hR0 hg0]
  have hgdeg : g.natDegree = 1 := by omega
  have hgsplit : g.Splits := Polynomial.splits_of_natDegree_le_one (by omega)
  have hgroots : g.roots.card = 1 := by
    rw [splits_iff_card_roots] at hgsplit
    omega
  obtain ⟨r, hr⟩ : ∃ r, r ∈ g.roots := by
    rw [← Multiset.card_pos_iff_exists_mem, hgroots]
    norm_num
  have hgr : (X - C r : ℝ[X]) ∣ g := by
    rw [dvd_iff_isRoot]
    exact (mem_roots hg0).1 hr |>.2
  set c : ℕ := Multiset.count r q.roots with hc
  have hcR : ((X - C r) ^ c : ℝ[X]) ∣ R := by
    have hle : Multiset.replicate c r ≤ q.roots := Multiset.le_count_iff_replicate_le.1 (le_refl c)
    have hmap : Multiset.map (fun a : ℝ => X - C a) (Multiset.replicate c r)
        = Multiset.replicate c (X - C r : ℝ[X]) := Multiset.map_replicate _ _ _
    have := Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle (f := fun a : ℝ => X - C a))
    rw [hmap, Multiset.prod_replicate] at this
    exact this
  have hcq : ((X - C r) ^ (c + 1) : ℝ[X]) ∣ q := by
    rw [hg, pow_succ]
    exact mul_dvd_mul hcR hgr
  have hle : c + 1 ≤ rootMultiplicity r q := (le_rootMultiplicity_iff hq).2 hcq
  rw [← count_roots] at hle
  omega

/-! ### The main theorem -/

theorem laguerreShift_ne_zero {β : ℝ} {p : ℝ[X]} (hp : p ≠ 0) (hn : 1 ≤ p.natDegree) :
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

end

end GaloisForLFunctions.HTGeometry
