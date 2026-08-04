import Mathlib

/-!
# A small value forces proximity to a root

Over the complex numbers a polynomial factors through its roots, so its modulus at a point is the
leading coefficient times the product of the distances to the roots.  If that modulus is small, the
smallest distance is small: the point is close to a root, quantitatively, with the degree as the
exponent.

This is the analytic substitute for a Newton--Puiseux place.  Applied to the top symbol of an
algebraic differential relation at a Wiman--Valiron point, it says that `f'(z)/f(z)` is
asymptotically a root of the top symbol — which is exactly what the Wiman place asserts, without
constructing a branch.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A common lower bound on the distances gives a lower bound on the modulus of the product. -/
theorem pow_card_le_norm_prod {s : Multiset ℂ} {T : ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ s, c ≤ ‖T - x‖) :
    c ^ Multiset.card s ≤ ‖(s.map (fun a => T - a)).prod‖ := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      have ha : c ≤ ‖T - a‖ := h a (Multiset.mem_cons_self a t)
      have ht : ∀ x ∈ t, c ≤ ‖T - x‖ := fun x hx => h x (Multiset.mem_cons_of_mem hx)
      have hrest := ih ht
      have hcpow : (0 : ℝ) ≤ c ^ Multiset.card t := by positivity
      have hprod : ‖((a ::ₘ t).map (fun a => T - a)).prod‖
          = ‖T - a‖ * ‖(t.map (fun a => T - a)).prod‖ := by
        simp [Multiset.map_cons, Multiset.prod_cons]
      rw [hprod, Multiset.card_cons, pow_succ]
      have hnn : (0 : ℝ) ≤ ‖(t.map (fun a => T - a)).prod‖ := norm_nonneg _
      calc c ^ Multiset.card t * c ≤ ‖(t.map (fun a => T - a)).prod‖ * c := by
            exact mul_le_mul_of_nonneg_right hrest hc
        _ ≤ ‖T - a‖ * ‖(t.map (fun a => T - a)).prod‖ := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right ha hnn

/-- **A small value forces proximity to a root.**  For a complex polynomial of degree at least one,
every point admits a root whose distance to it, raised to the degree and scaled by the leading
coefficient, is at most the modulus of the value. -/
theorem exists_root_pow_dist_le {Q : Polynomial ℂ} (hQ : 1 ≤ Q.natDegree) (T : ℂ) :
    ∃ r, Q.IsRoot r ∧ ‖T - r‖ ^ Q.natDegree * ‖Q.leadingCoeff‖ ≤ ‖Q.eval T‖ := by
  classical
  have hne : Q ≠ 0 := by
    intro h
    rw [h] at hQ
    simp at hQ
  have hsplits : Q.Splits := IsAlgClosed.splits Q
  have hcard : Multiset.card Q.roots = Q.natDegree :=
    (Polynomial.splits_iff_card_roots).mp hsplits
  have hpos : 0 < Multiset.card Q.roots := by
    rw [hcard]
    omega
  obtain ⟨a₀, ha₀⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  have hnonempty : Q.roots.toFinset.Nonempty := ⟨a₀, Multiset.mem_toFinset.mpr ha₀⟩
  obtain ⟨r₀, hr₀mem, hr₀min⟩ := Q.roots.toFinset.exists_min_image (fun r => ‖T - r‖) hnonempty
  have hr₀root : Q.IsRoot r₀ :=
    (Polynomial.mem_roots hne).mp (Multiset.mem_toFinset.mp hr₀mem)
  refine ⟨r₀, hr₀root, ?_⟩
  -- the factorisation
  have hfac : Q = C Q.leadingCoeff * (Q.roots.map fun a => X - C a).prod :=
    Polynomial.Splits.eq_prod_roots hsplits
  have heval : Q.eval T = Q.leadingCoeff * (Q.roots.map fun a => T - a).prod := by
    conv_lhs => rw [hfac]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod ?_
    refine Multiset.map_congr rfl ?_
    intro x _
    simp
  -- the minimal distance bounds every factor
  have hmin : ∀ x ∈ Q.roots, ‖T - r₀‖ ≤ ‖T - x‖ := by
    intro x hx
    exact hr₀min x (Multiset.mem_toFinset.mpr hx)
  have hbase := pow_card_le_norm_prod (T := T) (c := ‖T - r₀‖) (norm_nonneg _) hmin
  rw [hcard] at hbase
  rw [heval, norm_mul]
  have hlead : (0 : ℝ) ≤ ‖Q.leadingCoeff‖ := norm_nonneg _
  calc ‖T - r₀‖ ^ Q.natDegree * ‖Q.leadingCoeff‖
      = ‖Q.leadingCoeff‖ * ‖T - r₀‖ ^ Q.natDegree := by ring
    _ ≤ ‖Q.leadingCoeff‖ * ‖(Q.roots.map fun a => T - a).prod‖ :=
        mul_le_mul_of_nonneg_left hbase hlead

end GaloisForLFunctions.HTGeometry
