import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import GaloisForLFunctions.HTGeometry.ZetaTailClosedModulus

/-!
# Exact Gevrey order of a coefficient sequence

A coefficient sequence is Gevrey of order `r` when its terms are dominated by `C A ^ k (k!) ^ r`.
A lower bound of the same shape with a larger exponent, holding along an infinite set of indices,
rules out every smaller order: dividing the two bounds leaves a factorial power against a geometric
one, and the factorial wins.

Consequently a sequence with matching upper and lower Gevrey bounds of exponent `s` has `s` as its
**exact** order — it is Gevrey of order `s` and of no smaller order.  When `s` is irrational this is
the statement that contradicts the rationality of Newton-polygon slopes.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A coefficient sequence is Gevrey of order `r` when its terms obey a factorial bound of that
exponent. -/
def IsGevreyOfOrder (β : ℕ → ℝ) (r : ℝ) : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ k : ℕ, β k ≤ C * A ^ k * (Nat.factorial k : ℝ) ^ r

/-- A factorial eventually dominates every geometric sequence. -/
theorem eventually_lt_factorial (E D : ℝ) (hE : 0 < E) :
    ∀ᶠ k : ℕ in atTop, E * D ^ k < (Nat.factorial k : ℝ) := by
  have hzero : Tendsto (fun k : ℕ => D ^ k / (Nat.factorial k : ℝ)) atTop (𝓝 0) :=
    (Real.summable_pow_div_factorial D).tendsto_atTop_zero
  have hsmall : ∀ᶠ k : ℕ in atTop, D ^ k / (Nat.factorial k : ℝ) < E⁻¹ := by
    have hEinv : (0 : ℝ) < E⁻¹ := inv_pos.mpr hE
    exact hzero.eventually (eventually_lt_nhds hEinv)
  filter_upwards [hsmall] with k hk
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  rw [div_lt_iff₀ hfac] at hk
  calc E * D ^ k < E * (E⁻¹ * (Nat.factorial k : ℝ)) := by
        exact mul_lt_mul_of_pos_left hk hE
    _ = (Nat.factorial k : ℝ) := by
        field_simp

/-- **A factorial lower bound rules out every smaller Gevrey order.** -/
theorem not_isGevreyOfOrder_of_lower_bound {β : ℕ → ℝ} {s r : ℝ} (hrs : r < s)
    {c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hinf : {k : ℕ | c * a ^ k * (Nat.factorial k : ℝ) ^ s ≤ β k}.Infinite) :
    ¬ IsGevreyOfOrder β r := by
  classical
  rintro ⟨C, A, hC, hA, hbound⟩
  set δ : ℝ := s - r with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set E : ℝ := C / c with hEdef
  set B : ℝ := A / a with hBdef
  have hE : 0 < E := div_pos hC hc
  have hB : 0 < B := div_pos hA ha
  set E' : ℝ := E ^ (1 / δ) with hE'def
  set D : ℝ := B ^ (1 / δ) with hDdef
  have hE' : 0 < E' := Real.rpow_pos_of_pos hE _
  have hD : 0 < D := Real.rpow_pos_of_pos hB _
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_lt_factorial E' D hE')
  obtain ⟨k, hkmem, hkbig⟩ := hinf.exists_notMem_finset (Finset.range N)
  have hkge : N ≤ k := by
    by_contra hlt
    exact hkbig (Finset.mem_range.mpr (by omega))
  have hklarge : E' * D ^ k < (Nat.factorial k : ℝ) := hN k hkge
  have hfacpos : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hchain : c * a ^ k * (Nat.factorial k : ℝ) ^ s
      ≤ C * A ^ k * (Nat.factorial k : ℝ) ^ r := le_trans hkmem (hbound k)
  have hsplit : (Nat.factorial k : ℝ) ^ s
      = (Nat.factorial k : ℝ) ^ r * (Nat.factorial k : ℝ) ^ δ := by
    rw [← Real.rpow_add hfacpos]
    congr 1
    rw [hδdef]
    ring
  have hrpos : (0 : ℝ) < (Nat.factorial k : ℝ) ^ r := Real.rpow_pos_of_pos hfacpos _
  have hstep : c * a ^ k * (Nat.factorial k : ℝ) ^ δ ≤ C * A ^ k := by
    have hmul : (c * a ^ k * (Nat.factorial k : ℝ) ^ δ) * (Nat.factorial k : ℝ) ^ r
        ≤ (C * A ^ k) * (Nat.factorial k : ℝ) ^ r := by
      rw [hsplit] at hchain
      calc (c * a ^ k * (Nat.factorial k : ℝ) ^ δ) * (Nat.factorial k : ℝ) ^ r
          = c * a ^ k * ((Nat.factorial k : ℝ) ^ r * (Nat.factorial k : ℝ) ^ δ) := by ring
        _ ≤ C * A ^ k * (Nat.factorial k : ℝ) ^ r := hchain
        _ = (C * A ^ k) * (Nat.factorial k : ℝ) ^ r := by ring
    exact le_of_mul_le_mul_right hmul hrpos
  have hEB : (Nat.factorial k : ℝ) ^ δ ≤ E * B ^ k := by
    rw [hEdef, hBdef, div_pow, div_mul_div_comm, le_div_iff₀ (by positivity)]
    calc (Nat.factorial k : ℝ) ^ δ * (c * a ^ k)
        = c * a ^ k * (Nat.factorial k : ℝ) ^ δ := by ring
      _ ≤ C * A ^ k := hstep
  have hnn : (0 : ℝ) ≤ (Nat.factorial k : ℝ) ^ δ := le_of_lt (Real.rpow_pos_of_pos hfacpos _)
  have hmono := Real.rpow_le_rpow hnn hEB (le_of_lt (by positivity : (0 : ℝ) < 1 / δ))
  have hleft : ((Nat.factorial k : ℝ) ^ δ) ^ (1 / δ) = (Nat.factorial k : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hfacpos), mul_one_div_cancel (ne_of_gt hδ), Real.rpow_one]
  have hright : (E * B ^ k) ^ (1 / δ) = E' * D ^ k := by
    rw [Real.mul_rpow (le_of_lt hE) (le_of_lt (pow_pos hB k))]
    congr 1
    rw [hDdef, ← Real.rpow_natCast B k, ← Real.rpow_natCast (B ^ (1 / δ)) k,
      ← Real.rpow_mul (le_of_lt hB), ← Real.rpow_mul (le_of_lt hB)]
    congr 1
    ring
  rw [hleft, hright] at hmono
  exact absurd hklarge (not_lt.mpr hmono)

/-- Gevrey bounds weaken as the order grows. -/
theorem IsGevreyOfOrder.mono {β : ℕ → ℝ} {r r' : ℝ} (h : IsGevreyOfOrder β r) (hr : r ≤ r') :
    IsGevreyOfOrder β r' := by
  obtain ⟨C, A, hC, hA, hbound⟩ := h
  refine ⟨C, A, hC, hA, fun k => le_trans (hbound k) ?_⟩
  have hone : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hpow : (Nat.factorial k : ℝ) ^ r ≤ (Nat.factorial k : ℝ) ^ r' :=
    Real.rpow_le_rpow_of_exponent_le hone hr
  have hpos : (0 : ℝ) ≤ C * A ^ k := by positivity
  exact mul_le_mul_of_nonneg_left hpow hpos

/-- The exact Gevrey order of a coefficient modulus: Gevrey of that order and of no smaller one. -/
def IsExactGevreyOrder (β : ℕ → ℝ) (s : ℝ) : Prop :=
  IsGevreyOfOrder β s ∧ ∀ r : ℝ, r < s → ¬ IsGevreyOfOrder β r

/-- **Exact Gevrey order.**  Matching upper and lower factorial bounds of exponent `s` make `s` the
exact order: the sequence is Gevrey of order `s` and of no smaller order. -/
theorem isGevreyOfOrder_and_not_lt {β : ℕ → ℝ} {s : ℝ}
    (hupper : IsGevreyOfOrder β s)
    {c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hinf : {k : ℕ | c * a ^ k * (Nat.factorial k : ℝ) ^ s ≤ β k}.Infinite) :
    IsGevreyOfOrder β s ∧ ∀ r : ℝ, r < s → ¬ IsGevreyOfOrder β r :=
  ⟨hupper, fun _ hr => not_isGevreyOfOrder_of_lower_bound hr hc ha hinf⟩

/-- **The exact Gevrey order of the irrational-power zeta tail is `s`.**  It is Gevrey of order `s`
and of no smaller order, so its exact order is irrational. -/
theorem zetaTail_isGevreyOfOrder_exact {s : ℝ} (hs : 0 < s) (hirr : Irrational s) :
    IsExactGevreyOrder (fun k => |zetaTailModulus s k|) s := by
  obtain ⟨⟨C, A, hC, hA, hupper⟩, ⟨c, a, hc, ha, hinf⟩⟩ := gevrey_exact_order_zetaTail hs hirr
  exact isGevreyOfOrder_and_not_lt ⟨C, A, hC, hA, hupper⟩ hc ha hinf

end GaloisForLFunctions.HTGeometry
