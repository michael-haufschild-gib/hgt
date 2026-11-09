import GaloisForLFunctions.HyperbolicArakelovTheory.TheFinitePlacesAreTrees
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoprimeRenewal
import Mathlib.Analysis.PSeries

/-!
# The convergence boundary of a coupled adelic orbit diagonal

On a reduced rational torus displacement `a/b<1`, multiplying the critical
archimedean Green profile at distance `2 log(b/a)` by `1/(ab)` gives
`b⁻²/(1-(a/b)⁴)`. The latter finite factor is the product of the normalized
critical apartment factors. The identity displacement is excluded.

The height-damped orbit series converges exactly for positive damping.
Its divergence at zero damping comes from genuine nonidentity rational
displacements, so a free-space subtraction at the identity does not remove it.
This is a convergence theorem for the multiplicatively coupled local profile;
it does not identify that profile with Weil's form.
-/

noncomputable section
open Real Filter Topology
open GaloisForLFunctions.SurfaceOfSpecZ
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeRenewal

namespace GaloisForLFunctions.HyperbolicArakelovTheory.CoupledOrbit

/-- Positive rational displacements below one, indexed in lowest terms. -/
abbrev Primitive := Cone

/-- Height exponent `s`; the undamped critical product has `s=2`. -/
def term (s : ℝ) (q : Primitive) : ℝ :=
  (q.val.2 : ℝ) ^ (-s) / (1 - ((q.val.1 : ℝ) / q.val.2) ^ 4)

private theorem ratio_bounds (q : Primitive) :
    0 < (q.val.1 : ℝ) / q.val.2 ∧ (q.val.1 : ℝ) / q.val.2 < 1 := by
  have ha : (0 : ℝ) < q.val.1 := by exact_mod_cast q.property.1
  have hab : (q.val.1 : ℝ) < q.val.2 := by exact_mod_cast q.property.2.1
  exact ⟨div_pos ha (ha.trans hab), (div_lt_one (ha.trans hab)).mpr hab⟩

private theorem fourth_gap_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    1 - r ≤ 1 - r ^ 4 ∧ 1 - r ^ 4 ≤ 4 * (1 - r) := by
  have h2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
  have h3 : r ^ 3 ≤ 1 := pow_le_one₀ hr0 hr1
  have hlo : 1 ≤ 1 + r + r ^ 2 + r ^ 3 := by
    linarith only [hr0, sq_nonneg r, pow_nonneg hr0 3]
  have hhi : 1 + r + r ^ 2 + r ^ 3 ≤ 4 := by linarith only [hr1, h2, h3]
  have hfactor : 1 - r ^ 4 = (1 - r) * (1 + r + r ^ 2 + r ^ 3) := by ring
  rw [hfactor]
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hr1)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr hr1)

theorem term_pos (s : ℝ) (q : Primitive) : 0 < term s q := by
  have h := ratio_bounds q
  have hb : (0 : ℝ) < q.val.2 := by exact_mod_cast (q.property.1.trans q.property.2.1)
  exact div_pos (Real.rpow_pos_of_pos hb _) ((sub_pos.mpr h.2).trans_le
    (fourth_gap_bounds h.1.le h.2.le).1)

/-- Exact critical product on a rational torus displacement. -/
theorem term_two_eq_green_product (q : Primitive) :
    term 2 q = archProfile (2 * Real.log ((q.val.2 : ℝ) / q.val.1)) /
      ((q.val.1 : ℝ) * q.val.2) := by
  have ha : (0 : ℝ) < q.val.1 := by exact_mod_cast q.property.1
  have hb : (0 : ℝ) < q.val.2 := by exact_mod_cast (q.property.1.trans q.property.2.1)
  have he : Real.exp (-Real.log ((q.val.2 : ℝ) / q.val.1)) =
      (q.val.1 : ℝ) / q.val.2 := by
    rw [Real.exp_neg, Real.exp_log (div_pos hb ha), inv_div]
  have he4 : Real.exp (-2 * (2 * Real.log ((q.val.2 : ℝ) / q.val.1))) =
      ((q.val.1 : ℝ) / q.val.2) ^ 4 := by
    rw [← he, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [archProfile, show -(2 * Real.log ((q.val.2 : ℝ) / q.val.1)) / 2 =
    -Real.log ((q.val.2 : ℝ) / q.val.1) by ring, he, he4]
  unfold term
  rw [Real.rpow_neg hb.le, Real.rpow_two]
  field_simp [ha.ne', hb.ne']

/-- A product of two one-dimensional summable powers controls the whole cone. -/
theorem term_le_product {s : ℝ} (hs : 2 < s) (q : Primitive) :
    term s q ≤ (q.val.1 : ℝ) ^ (-(s / 2)) *
      ((q.val.2 - q.val.1 : ℕ) : ℝ) ^ (-(s / 2)) := by
  have ha : (0 : ℝ) < q.val.1 := by exact_mod_cast q.property.1
  have hab : (q.val.1 : ℝ) < q.val.2 := by exact_mod_cast q.property.2.1
  have hb : (0 : ℝ) < q.val.2 := ha.trans hab
  have hk : 0 < (q.val.2 : ℝ) - q.val.1 := sub_pos.mpr hab
  rw [Nat.cast_sub q.property.2.1.le]
  have hr := ratio_bounds q
  have hden := (fourth_gap_bounds hr.1.le hr.2.le).1
  have hgap : 1 - (q.val.1 : ℝ) / q.val.2 =
      ((q.val.2 : ℝ) - q.val.1) / q.val.2 := by field_simp [hb.ne']
  have hfirst : term s q ≤ (q.val.2 : ℝ) ^ (1 - s) /
      ((q.val.2 : ℝ) - q.val.1) := by
    calc
      term s q ≤ (q.val.2 : ℝ) ^ (-s) / (1 - (q.val.1 : ℝ) / q.val.2) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hb.le _) (sub_pos.mpr hr.2) hden
      _ = _ := by
        rw [hgap, Real.rpow_sub hb, Real.rpow_one, Real.rpow_neg hb.le]
        field_simp [hb.ne', hk.ne']
  have hpow : (q.val.2 : ℝ) ^ (1 - s) =
      (q.val.2 : ℝ) ^ (-(s / 2)) * (q.val.2 : ℝ) ^ (1 - s / 2) := by
    rw [← Real.rpow_add hb]
    congr 1
    ring
  have hleft := Real.rpow_le_rpow_of_nonpos ha hab.le (show -(s / 2) ≤ 0 by linarith only [hs])
  have hright := Real.rpow_le_rpow_of_nonpos hk
    (show (q.val.2 : ℝ) - q.val.1 ≤ q.val.2 by linarith only [ha])
    (show 1 - s / 2 ≤ 0 by linarith only [hs])
  calc
    term s q ≤ (q.val.2 : ℝ) ^ (1 - s) / ((q.val.2 : ℝ) - q.val.1) := hfirst
    _ ≤ ((q.val.1 : ℝ) ^ (-(s / 2)) *
        ((q.val.2 : ℝ) - q.val.1) ^ (1 - s / 2)) /
          ((q.val.2 : ℝ) - q.val.1) := by
      rw [hpow]
      exact div_le_div_of_nonneg_right
        (mul_le_mul hleft hright (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg ha.le _)) hk.le
    _ = _ := by
      rw [show 1 - s / 2 = -(s / 2) + 1 by ring, Real.rpow_add hk, Real.rpow_one]
      field_simp [hk.ne']

private theorem cone_index_injective :
    Function.Injective (fun q : Primitive => (q.val.1, q.val.2 - q.val.1)) := by
  intro p q h
  have ha := congrArg Prod.fst h
  have hk := congrArg Prod.snd h
  have hp := p.property
  have hq := q.property
  apply Subtype.ext
  apply Prod.ext
  · exact ha
  · dsimp only at ha hk
    omega

theorem summable_term {s : ℝ} (hs : 2 < s) : Summable (term s) := by
  have hpow : Summable (fun n : ℕ => (n : ℝ) ^ (-(s / 2))) :=
    Real.summable_nat_rpow.mpr (by linarith only [hs])
  have hp := hpow.mul_of_nonneg hpow
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact (hp.comp_injective cone_index_injective).of_nonneg_of_le
    (fun q => (term_pos s q).le) (term_le_product hs)

/-- Consecutive primitive pairs approach the identity in the real factor. -/
def consecutive (k : ℕ) : Primitive :=
  ⟨(k + 1, k + 2), by omega, by omega, by
    change Nat.Coprime (k + 1) ((k + 1) + 1)
    simp⟩

theorem consecutive_injective : Function.Injective consecutive := by
  intro k l h
  have hk := congrArg (fun q : Primitive => q.val.1) h
  change k + 1 = l + 1 at hk
  omega

/-- The nonidentity critical orbit already contains a harmonic divergent subseries. -/
theorem reciprocal_le_consecutive (k : ℕ) :
    1 / ((k : ℝ) + 2) ≤ 4 * term 2 (consecutive k) := by
  have hr := ratio_bounds (consecutive k)
  have hden := (fourth_gap_bounds hr.1.le hr.2.le).2
  have hpos : 0 < 1 - ((((k + 1 : ℕ) : ℝ) / (k + 2 : ℕ)) ^ 4) :=
    (sub_pos.mpr hr.2).trans_le (fourth_gap_bounds hr.1.le hr.2.le).1
  change 1 - ((((k + 1 : ℕ) : ℝ) / (k + 2 : ℕ)) ^ 4) ≤
    4 * (1 - (((k + 1 : ℕ) : ℝ) / (k + 2 : ℕ))) at hden
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hden hpos
  have hb : 0 < (k : ℝ) + 2 := by positivity
  unfold term consecutive
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [Real.rpow_neg hb.le, Real.rpow_two]
  have hgap : 1 - ((k : ℝ) + 1) / (k + 2) = 1 / (k + 2) := by
    field_simp
    ring
  rw [hgap, mul_one_div] at hden
  have hc := (le_div_iff₀ hb).mp hden
  rw [show 4 * ((((k : ℝ) + 2) ^ 2)⁻¹ /
      (1 - (((k : ℝ) + 1) / (k + 2)) ^ 4)) =
      4 / (((k : ℝ) + 2) ^ 2 * (1 - (((k : ℝ) + 1) / (k + 2)) ^ 4)) by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring]
  apply (div_le_div_iff₀ hb (mul_pos (sq_pos_of_pos hb) hpos)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hc hb.le]

theorem not_summable_term_two : ¬ Summable (term 2) := by
  intro h
  have hseq := (h.comp_injective consecutive_injective).mul_left 4
  have hi : Summable (fun k : ℕ => 1 / ((k : ℝ) + 2)) :=
    hseq.of_nonneg_of_le (fun k => by positivity) reciprocal_le_consecutive
  have hshift : Summable (fun k : ℕ => ((k + 2 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat, Real.rpow_neg_one, one_div] using hi
  have hbase := (summable_nat_add_iff
    (f := fun k : ℕ => (k : ℝ) ^ (-1 : ℝ)) 2).mp hshift
  have hbad := Real.summable_nat_rpow.mp hbase
  exact (lt_irrefl (-1 : ℝ)) hbad

/-- Sharp abscissa for the genuinely coupled rational orbit. -/
theorem summable_term_iff (s : ℝ) : Summable (term s) ↔ 2 < s := by
  constructor
  · intro h
    by_contra hs
    have hs2 : s ≤ 2 := le_of_not_gt hs
    apply not_summable_term_two
    apply h.of_nonneg_of_le (fun q => (term_pos 2 q).le)
    intro q
    have hb : (1 : ℝ) ≤ q.val.2 := by
      exact_mod_cast (show 1 ≤ q.val.2 by have hp := q.property; omega)
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hb (neg_le_neg hs2))
      ((sub_pos.mpr (ratio_bounds q).2).trans_le
        (fourth_gap_bounds (ratio_bounds q).1.le (ratio_bounds q).2.le).1).le
  · exact summable_term

/-- The normalized critical tree Green function at an even apartment distance. -/
theorem normalized_treeGreen_even {p : ℕ} (hp : p.Prime) (k : ℕ) :
    treeGreen p (1 / 2) (2 * k) / treeGreen p (1 / 2) 0 =
      ((p : ℝ) ^ k)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hcoeff : (p : ℝ) ^ (1 / 2 : ℝ) / ((p : ℝ) ^ (2 * (1 / 2) : ℝ) - 1) ≠ 0 := by
    norm_num only [mul_one_div_cancel, Real.rpow_one]
    exact div_ne_zero (Real.rpow_pos_of_pos hp0 _).ne' (by linarith only [hp1])
  unfold treeGreen
  rw [pow_zero, mul_one, mul_div_cancel_left₀ _ hcoeff]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  have he : -(1 / 2 : ℝ) * ((2 * k : ℕ) : ℝ) = -(k : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg hp0.le, Real.rpow_natCast]

/-- Finite places of an integral torus displacement, with the local diagonal divided out. -/
def finiteFactor (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors,
    treeGreen p (1 / 2) (2 * n.factorization p) / treeGreen p (1 / 2) 0

theorem finiteFactor_eq_inv {n : ℕ} (hn : n ≠ 0) : finiteFactor n = (n : ℝ)⁻¹ := by
  unfold finiteFactor
  rw [Finset.prod_congr rfl (fun p hp =>
    normalized_treeGreen_even (Nat.prime_of_mem_primeFactors hp) (n.factorization p)),
    Finset.prod_inv_distrib]
  congr 1
  exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm

/-- The critical orbit summand is a product of the actual local Green profiles. -/
theorem term_two_eq_local_product (q : Primitive) :
    term 2 q = archProfile (2 * Real.log ((q.val.2 : ℝ) / q.val.1)) *
      finiteFactor q.val.1 * finiteFactor q.val.2 := by
  rw [term_two_eq_green_product, finiteFactor_eq_inv (Nat.ne_of_gt q.property.1),
    finiteFactor_eq_inv (Nat.ne_of_gt (q.property.1.trans q.property.2.1))]
  ring

/-- The smooth remainder after extracting the real collision pole. -/
def regularProfile (r : ℝ) : ℝ := 1 / (4 * (1 + r)) + 1 / (2 * (1 + r ^ 2))

theorem profile_split {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    1 / (1 - r ^ 4) = 1 / (4 * (1 - r)) + regularProfile r := by
  have h1 : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
  have h2 : 1 + r ≠ 0 := by positivity
  have h3 : 1 + r ^ 2 ≠ 0 := by positivity
  have h4 : 1 - r ^ 4 ≠ 0 := ((sub_pos.mpr hr1).trans_le
    (fourth_gap_bounds hr0 hr1.le).1).ne'
  unfold regularProfile
  field_simp
  ring

theorem regularProfile_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    3 / 8 ≤ regularProfile r ∧ regularProfile r ≤ 3 / 4 := by
  have hsq : r ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
  have h1lo : (1 : ℝ) / 8 ≤ 1 / (4 * (1 + r)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith only [hr1])
  have h2lo : (1 : ℝ) / 4 ≤ 1 / (2 * (1 + r ^ 2)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith only [hsq])
  have h1hi : 1 / (4 * (1 + r)) ≤ (1 : ℝ) / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith only [hr0])
  have h2hi : 1 / (2 * (1 + r ^ 2)) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith only [sq_nonneg r])
  unfold regularProfile
  constructor <;> linarith only [h1lo, h2lo, h1hi, h2hi]

/-- Each rational summand splits into its collision pole and a smooth positive part. -/
theorem term_split (s : ℝ) (q : Primitive) :
    term s q = (q.val.2 : ℝ) ^ (1 - s) / (4 * ((q.val.2 : ℝ) - q.val.1)) +
      (q.val.2 : ℝ) ^ (-s) * regularProfile ((q.val.1 : ℝ) / q.val.2) := by
  have hb : (0 : ℝ) < q.val.2 := by exact_mod_cast (q.property.1.trans q.property.2.1)
  have hk : (0 : ℝ) < (q.val.2 : ℝ) - q.val.1 := by
    have hab : (q.val.1 : ℝ) < q.val.2 := by exact_mod_cast q.property.2.1
    exact sub_pos.mpr hab
  have hr := ratio_bounds q
  rw [term, div_eq_mul_one_div, profile_split hr.1.le hr.2, mul_add]
  congr 1
  rw [Real.rpow_sub hb, Real.rpow_one, Real.rpow_neg hb.le]
  field_simp

#print axioms term_two_eq_local_product
#print axioms term_split
#print axioms term_two_eq_green_product
#print axioms term_le_product
#print axioms reciprocal_le_consecutive
#print axioms summable_term_iff

end GaloisForLFunctions.HyperbolicArakelovTheory.CoupledOrbit
