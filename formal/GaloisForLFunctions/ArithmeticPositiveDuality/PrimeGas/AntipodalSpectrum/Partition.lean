import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.PrimitiveRays
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.GeometricFactor

/-!
# Exact partition of the antipodal rejection

Summing the common radial label gives ζ(2s). Summing the missing windings
in both orientations gives a nonvanishing geometric factor. The same block
and winding order work at every complex inverse temperature.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture.Binary
open scoped Classical

abbrev ExceptionalTime := {t : ℝ // t ∈ exceptional}

private theorem height_gt_one {a b : ℕ+} (hne : a ≠ b) : 1 < (a*b).val := by
  have hl : a.val ≤ a.val*b.val := Nat.le_mul_of_pos_right _ b.pos
  have hr : b.val ≤ a.val*b.val := Nat.le_mul_of_pos_left _ a.pos
  have hn : a.val ≠ b.val := fun h => hne (PNat.coe_injective h)
  change 1 < a.val*b.val
  have ha := a.pos
  have hb := b.pos
  omega

theorem heat_contraction (B : ℕ+) (hB : 1 < B.val) (s : ℂ) (hs : 0 < s.re) : ‖heat s B‖ < 1 := by
  rw [norm_heat,Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs) (Real.log_pos (by exact_mod_cast hB))

/-- One primitive occupation basis supplies the block and order in the trace at all temperatures. -/
theorem spectral_coordinates (t : ExceptionalTime) : ∃ (a b : ℕ+) (m : ℕ),
    a.Coprime b ∧ a ≠ b ∧ 1 < m ∧ (∃ j : ℕ, m = 2^j) ∧
    (∃ e : (Bool × (Missing m × ℕ+)) ≃ {x // rejected t.val x}, ∀ p, (e p).val = ray a b p.1 p.2.1.val p.2.2) ∧
    ∀ s : {s : ℂ // 1/2 < s.re}, correction t.val s.val = riemannZeta (2*s.val)*factor m (heat s.val (a*b)) := by
  obtain ⟨a,b,m,hc,hd,hm,hpow,e,he⟩ := rejected_basis t
  refine ⟨a,b,m,hc,hd,hm,hpow,⟨e,he⟩,fun s => ?_⟩
  let q := heat s.val (a*b)
  let W (p : Missing m × ℕ+) := q^p.1.val*heat (2*s.val) p.2
  have hw (p : Bool × (Missing m × ℕ+)) : wordHeat s.val (e p).val = W p.2 := by
    rw [he,ray_heat]
  have hs := ((sectorHeat_iff _ _).mp ((rejected_heat_iff t.val s.val).mpr fun _ => s.property)).of_norm
  have hs' : Summable (fun p : Bool × (Missing m × ℕ+) => W p.2) :=
    (hs.comp_injective (i := e) e.injective).congr hw
  have hrow : Summable W := hs'.comp_injective (i := fun p => (false,p)) (fun _ _ h => congrArg Prod.snd h)
  have hβ : 1 < (2*s.val).re := by rw [two_mul,Complex.add_re]; linarith only [s.property]
  have hz : ∑' n : ℕ+, heat (2*s.val) n = riemannZeta (2*s.val) := (heat_hasSum ⟨_,hβ⟩).tsum_eq
  have hsum : ∑' p, W p = (∑' k : Missing m, q^k.val)*riemannZeta (2*s.val) := by
    rw [hrow.tsum_prod]
    simp only [W,tsum_mul_left,hz,tsum_mul_right]
  have hq : ‖q‖ < 1 := heat_contraction _ (height_gt_one hd) _ (by linarith only [s.property])
  calc
    correction t.val s.val = ∑' p, wordHeat s.val (e p).val := (e.tsum_eq _).symm
    _ = ∑' p : Bool × (Missing m × ℕ+), W p.2 := tsum_congr hw
    _ = ∑' _r : Bool, ∑' p, W p := hs'.tsum_prod
    _ = riemannZeta (2*s.val)*factor m q := by
      rw [tsum_bool,hsum,← twice_missing_sum hq hm]
      ring

theorem partition_exists (t : ExceptionalTime) : ∃ (B : ℕ+) (m : ℕ), 1 < B.val ∧ 1 < m ∧
    (∃ j : ℕ, m = 2^j) ∧ ∀ s : {s : ℂ // 1/2 < s.re},
      correction t.val s.val = riemannZeta (2*s.val)*factor m (heat s.val B) := by
  obtain ⟨a,b,m,_,hd,hm,hpow,_,ht⟩ := spectral_coordinates t
  exact ⟨a*b,m,height_gt_one hd,hm,hpow,ht⟩

/-- A single reduced direction supplies both the occupations and the trace. -/
private structure Spectrum (t : ExceptionalTime) where
  a : ℕ+
  b : ℕ+
  m : ℕ
  coprime : a.Coprime b
  distinct : a ≠ b
  nontrivial : 1 < m
  dyadic : ∃ j : ℕ, m = 2^j
  basis : ∃ e : (Bool × (Missing m × ℕ+)) ≃ {x // rejected t.val x},
    ∀ p, (e p).val = ray a b p.1 p.2.1.val p.2.2
  trace_eq : ∀ s : {s : ℂ // 1/2 < s.re},
    correction t.val s.val = riemannZeta (2*s.val)*factor m (heat s.val (a*b))

private def spectrum (t : ExceptionalTime) : Spectrum t := Classical.choice (by
  obtain ⟨a,b,m,hc,hd,hm,hpow,he,hs⟩ := spectral_coordinates t
  exact ⟨⟨a,b,m,hc,hd,hm,hpow,he,hs⟩⟩)

def block (t : ExceptionalTime) := (spectrum t).a*(spectrum t).b
def windingOrder (t : ExceptionalTime) := (spectrum t).m

theorem block_basis (t : ExceptionalTime) : ∃ a b : ℕ+, a.Coprime b ∧ a ≠ b ∧ a*b = block t ∧
    ∃ e : (Bool × (Missing (windingOrder t) × ℕ+)) ≃ {x // rejected t.val x},
      ∀ p, (e p).val = ray a b p.1 p.2.1.val p.2.2 :=
  ⟨_,_,(spectrum t).coprime,(spectrum t).distinct,rfl,(spectrum t).basis⟩

theorem block_nontrivial (t : ExceptionalTime) : 1 < (block t).val := height_gt_one (spectrum t).distinct
theorem order_nontrivial (t : ExceptionalTime) : 1 < windingOrder t := (spectrum t).nontrivial
theorem order_dyadic (t : ExceptionalTime) : ∃ j : ℕ, windingOrder t = 2^j := (spectrum t).dyadic

/-- Continuation specified by the physical block and winding order. -/
def response (t : ExceptionalTime) (s : ℂ) := riemannZeta (2*s)*factor (windingOrder t) (heat s (block t))

theorem response_eq_heat_sum (t : ExceptionalTime) (s : {s : ℂ // 1/2 < s.re}) :
    correction t.val s.val = response t s.val := (spectrum t).trace_eq s

/-- The continued response agrees with the operator trace on its entire trace-class domain. -/
theorem response_trace (t : ExceptionalTime) (s : {s : ℂ // AbsoluteHeat (rejected t.val) s}) :
    ContinuousLinearMap.opTrace (sectorHeat (rejected t.val) s) = response t s.val := by
  have hs := (rejected_heat_iff t.val s.val).mp ((sectorHeat_iff _ _).mpr s.property) t.property
  exact (operator_trace _ s).trans (response_eq_heat_sum t ⟨s.val,hs⟩)

#print axioms spectral_coordinates
#print axioms block_basis
#print axioms partition_exists
#print axioms response_eq_heat_sum
#print axioms response_trace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
