import GaloisForLFunctions.FiniteFreeProbability.WalshHalfPlaneTheorem
import GaloisForLFunctions.FiniteFreeProbability.HermiteHeatOperator
import GaloisForLFunctions.RHTower.XiJensenHermiteLimit
import GaloisForLFunctions.HTGeometry.HermiteSignChanges
import GaloisForLFunctions.HTGeometry.HermitePerturbationRealRoots
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# The shift regime: Jensen polynomials of `Ξ` are asymptotically semicircular

The heat operators `e^{sD²}` on polynomials of degree `≤ d` form a group:
`e^{sD²} e^{s'D²} = e^{(s+s')D²}`, because their symbols are truncations of the Gaussian power
series `G_s = expand₂ (e^{sX})` and `expand₂` is a ring map. The probabilists' Hermite polynomial is
`He_d = e^{−D²/2} X^d`; forward heat (`s ≤ 0`) is `⊞_d` against a real-rooted scaled Hermite
polynomial, so by Walsh it preserves real-rootedness. Hence the set of backward heat times keeping
a polynomial real-rooted is an interval `(−∞, κ]`, its *Gaussian capacity*; for `He_d` it is `1/2`.

**Theorem.** For every fixed degree `d` and every `s < 1/2`, the normalized shifted Jensen
polynomials `J̃^{d,n}` of `Ξ` satisfy: `e^{sD²} J̃^{d,n}` is real-rooted for all large `n`. Equivalently
`J^{d,n}` has a Gaussian `⊞`-component carrying any fraction `< 1` of the Hermite variance.

This is the dual of the finite free de Bruijn–Newman law: in the shift regime (`n → ∞`, `d` fixed)
the Jensen polynomials are almost purely semicircular, while in the degree regime (`d → ∞`) their
Gaussian capacity is `o(d^{-2})`.
-/

open Polynomial Filter Topology Finset
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-! ## The heat group -/

/-- The Gaussian power series `Σ_m s^m X^{2m}/m!`. -/
def gaussSeries (s : ℝ) : PowerSeries ℝ :=
  PowerSeries.expand 2 two_ne_zero (PowerSeries.rescale s (PowerSeries.exp ℝ))

theorem coeff_gaussSeries (s : ℝ) (n : ℕ) :
    PowerSeries.coeff n (gaussSeries s) =
      if 2 ∣ n then s ^ (n / 2) / ((n / 2).factorial : ℝ) else 0 := by
  rw [gaussSeries, PowerSeries.coeff_expand]
  split_ifs
  · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    simp [div_eq_mul_inv, mul_comm]
  · rfl

theorem gaussSeries_add (s s' : ℝ) : gaussSeries s * gaussSeries s' = gaussSeries (s + s') := by
  rw [gaussSeries, gaussSeries, ← map_mul, PowerSeries.exp_mul_exp_eq_exp_add, gaussSeries]

theorem coeff_heatSymbol (s : ℝ) (d n : ℕ) (hn : n ≤ d) :
    (heatSymbol s d).coeff n = PowerSeries.coeff n (gaussSeries s) := by
  rw [heatSymbol, finsetSum_coeff, coeff_gaussSeries]
  split_ifs with h2
  · obtain ⟨m, rfl⟩ := h2
    rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hk; rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    · intro hm; exact absurd (Finset.mem_range.2 (by omega)) hm
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => h2 ⟨k, h⟩), mul_zero]

theorem heatOp_eq_diffOp_trunc {s : ℝ} {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    heatOp s d p = diffOp (PowerSeries.trunc (d + 1) (gaussSeries s)) p := by
  rw [heatOp]
  refine diffOp_congr hp fun i hi => ?_
  rw [coeff_heatSymbol s d i hi, PowerSeries.coeff_trunc, if_pos (by omega)]

theorem natDegree_heatOp_le (s : ℝ) (d : ℕ) (p : ℝ[X]) : (heatOp s d p).natDegree ≤ p.natDegree :=
  natDegree_diffOp_le _ _

/-- **The heat group law.** -/
theorem heatOp_heatOp {s s' : ℝ} {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    heatOp s d (heatOp s' d p) = heatOp (s + s') d p := by
  rw [heatOp_eq_diffOp_trunc ((natDegree_heatOp_le _ _ _).trans hp), heatOp_eq_diffOp_trunc hp,
    ← diffOp_mul, heatOp_eq_diffOp_trunc hp]
  refine diffOp_congr hp fun i hi => ?_
  rw [← Polynomial.coeff_coe, Polynomial.coe_mul,
    ← PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc _ _ (Nat.lt_succ_of_le hi), gaussSeries_add,
    PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_of_le hi)]

theorem coeff_heatOp (s : ℝ) (d : ℕ) (p : ℝ[X]) (j : ℕ) :
    (heatOp s d p).coeff j = ∑ k ∈ Finset.range (d + 1),
      s ^ k / (k.factorial : ℝ) * (((j + 2 * k).descFactorial (2 * k) : ℕ) : ℝ) *
        p.coeff (j + 2 * k) := by
  rw [heatOp_eq_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul]
  ring

theorem coeff_hermiteFF_self (u : ℝ) (d : ℕ) : (hermiteFF u d).coeff d = 1 := by
  rw [hermiteFF, coeff_heatOp, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk; rw [coeff_X_pow, if_neg (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos d)) h

/-! ## Affine changes of variable and Hermite polynomials -/

theorem iterate_derivative_comp_affine (p : ℝ[X]) (a b : ℝ) (k : ℕ) :
    derivative^[k] (p.comp (C a * X + C b)) = C (a ^ k) * (derivative^[k] p).comp (C a * X + C b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp,
      Function.iterate_succ_apply']
    simp only [derivative_add, derivative_C_mul_X, derivative_C, add_zero, pow_succ, map_mul]
    ring

/-- `e^{sD²}` intertwines affine substitutions: slope `a` rescales the time by `a²`. -/
theorem heatOp_comp_affine (s a b : ℝ) (d : ℕ) (p : ℝ[X]) :
    heatOp s d (p.comp (C a * X + C b)) = (heatOp (s * a ^ 2) d p).comp (C a * X + C b) := by
  rw [heatOp_eq_sum, heatOp_eq_sum, Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_derivative_comp_affine, mul_comp, C_comp, ← mul_assoc, ← C_mul, mul_pow, pow_mul]
  congr 2
  ring

/-- The Hermite polynomial is the forward heat flow of `X^d` by time `1/2`. -/
theorem hermiteReal_eq_heatOp (d : ℕ) : hermiteReal d = heatOp (-(1 / 2)) d (X ^ d) := by
  have h := realHermite_eq_sum d
  change realHermite d = _
  rw [h, heatOp_eq_sum]
  simp only [iterate_derivative_X_pow_eq_C_mul, ← mul_assoc, ← C_mul]
  rw [← Finset.sum_subset (Finset.range_mono (show d / 2 + 1 ≤ d + 1 by omega))]
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm2 : 2 * m ≤ d := by have := Finset.mem_range.1 hm; omega
    congr 2
    have hc := hermiteCoeff_mul_two_pow hm2
    have hdesc : (d.descFactorial (2 * m) : ℝ) * ((d - 2 * m).factorial : ℝ) = d.factorial := by
      rw [mul_comm]; exact_mod_cast Nat.factorial_mul_descFactorial hm2
    have hmf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hkf : ((d - 2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : (2 : ℝ) ^ m ≠ 0 := by positivity
    rw [← hdesc] at hc
    rw [show (-(1 / 2 : ℝ)) = (-1) / 2 by norm_num, div_pow]
    field_simp
    field_simp at hc
    linear_combination hc
  · intro m _ hm
    have : d < 2 * m := by
      by_contra h; exact hm (Finset.mem_range.2 (by omega))
    rw [Nat.descFactorial_eq_zero_iff_lt.2 this]; simp

/-- Forward heat by `u > 0` of `X^d` is a rescaled Hermite polynomial. -/
theorem hermiteFF_neg_eq (d : ℕ) {u : ℝ} (hu : 0 < u) :
    hermiteFF (-u) d = C (Real.sqrt (2 * u) ^ d) *
      (hermiteReal d).comp (C (Real.sqrt (2 * u))⁻¹ * X + C 0) := by
  set c := Real.sqrt (2 * u)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 2 * u := Real.sq_sqrt (by positivity)
  have hX : (X ^ d : ℝ[X]) = C (c ^ d) * (X ^ d).comp (C c⁻¹ * X + C 0) := by
    simp only [X_pow_comp, map_zero, add_zero, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]
    rw [← mul_pow, mul_inv_cancel₀ hc.ne', one_pow, C_1, one_mul]
  rw [hermiteFF, hX, heatOp_C_mul, heatOp_comp_affine, hermiteReal_eq_heatOp]
  congr 3
  rw [inv_pow, hc2]
  field_simp

/-- Forward heat flows of `X^d` are real-rooted. -/
theorem splits_hermiteFF_of_nonpos {u : ℝ} (hu : u ≤ 0) (d : ℕ) : (hermiteFF u d).Splits := by
  rcases hu.lt_or_eq with hlt | rfl
  · have := hermiteFF_neg_eq d (u := -u) (by linarith)
    rw [neg_neg] at this
    rw [this]
    refine (Polynomial.Splits.C _).mul ?_
    exact (splits_iff_comp_splits_of_natDegree_eq_one (by
      rw [map_zero, add_zero, natDegree_C_mul_X _ (inv_ne_zero (Real.sqrt_pos.2 (by linarith)).ne')]
      )).1 (splits_hermiteReal d)
  · rw [hermiteFF, heatOp_eq_sum, Finset.sum_eq_single 0]
    · simp
    · intro k _ hk; simp [zero_pow hk]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos d)) h

/-- **Forward heat preserves real-rootedness** (Walsh against a real-rooted Hermite polynomial). -/
theorem splits_heatOp_of_nonpos {u : ℝ} (hu : u ≤ 0) {d : ℕ} {p : ℝ[X]} (hp : p.Splits)
    (hpd : p.natDegree ≤ d) : (heatOp u d p).Splits := by
  by_cases hp0 : p = 0
  · simp [hp0, heatOp, diffOp]
  have hcongr : heatOp u d p = heatOp u p.natDegree p := by
    rw [heatOp_eq_diffOp_trunc hpd, heatOp_eq_diffOp_trunc le_rfl]
    refine diffOp_congr le_rfl fun i hi => ?_
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos (by omega), if_pos (by omega)]
  rw [hcongr, heatOp_eq_ffConv le_rfl]
  have hH : hermiteFF u p.natDegree ≠ 0 := fun h0 => by
    have := coeff_hermiteFF_self u p.natDegree
    rw [h0, coeff_zero] at this
    exact zero_ne_one this
  exact splits_ffConv hp (splits_hermiteFF_of_nonpos hu _) hp0 rfl hH
    ((natDegree_heatOp_le _ _ _).trans (natDegree_X_pow_le _))

/-- **Gaussian capacity is an interval.** If `e^{sD²}p` is real-rooted, so is `e^{s'D²}p` for
every `s' ≤ s`. -/
theorem splits_heatOp_of_le {s s' : ℝ} (hss : s' ≤ s) {d : ℕ} {p : ℝ[X]} (hpd : p.natDegree ≤ d)
    (h : (heatOp s d p).Splits) : (heatOp s' d p).Splits := by
  have := splits_heatOp_of_nonpos (u := s' - s) (by linarith) h
    ((natDegree_heatOp_le _ _ _).trans hpd)
  rwa [heatOp_heatOp hpd, sub_add_cancel] at this

/-! ## Persistence of simple real roots -/

/-- Sign changes at `d` separated points force `d` real roots. -/
theorem splits_of_separated_sign_changes (P : ℝ[X]) (Z : Finset ℝ) {ε : ℝ} (hε : 0 < ε)
    (hdeg : P.natDegree ≤ Z.card) (hsign : ∀ z ∈ Z, P.eval (z - ε) * P.eval (z + ε) < 0)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * ε < |z - w|) : P.Splits := by
  classical
  by_cases hP : P = 0
  · subst P; exact Polynomial.Splits.zero
  have hroot : ∀ z ∈ Z, ∃ r ∈ Set.Ioo (z - ε) (z + ε), P.IsRoot r :=
    fun z hz => GaloisForLFunctions.SignAlternation.exists_root_of_sign_change (by linarith)
      (hsign z hz)
  choose! r hr hPr using hroot
  have hinj : Set.InjOn r Z := by
    intro z hz w hw heq
    by_contra hne
    have hab : |z - w| < 2 * ε := by
      have h1 := hr z hz; have h2 := hr w hw
      rw [abs_lt]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, heq]
    exact (not_lt_of_ge hab.le) (hsep z hz w hw hne)
  have hcard : Z.card ≤ P.roots.toFinset.card :=
    Finset.card_le_card_of_injOn r (fun z hz => by
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hP]; exact hPr z hz) hinj
  have h1 := Multiset.toFinset_card_le P.roots
  have h2 := Polynomial.card_roots' P
  rw [splits_iff_card_roots]
  omega

/-- **Simple real roots persist.** If `p_n → q` coefficientwise, `deg p_n ≤ d`, and `q` has `d`
distinct real roots, then `p_n` is real-rooted for all large `n`. -/
theorem eventually_splits_of_tendsto_coeff {q : ℝ[X]} {d : ℕ} (hq0 : q ≠ 0)
    (hqd : q.natDegree ≤ d) (hnd : q.roots.Nodup) (hcard : Multiset.card q.roots = d)
    {p : ℕ → ℝ[X]} (hpdeg : ∀ n, (p n).natDegree ≤ d)
    (hconv : ∀ j, Tendsto (fun n => (p n).coeff j) atTop (𝓝 (q.coeff j))) :
    ∀ᶠ n in atTop, (p n).Splits := by
  classical
  set Z := q.roots.toFinset
  have hZcard : Z.card = d := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  have heval : ∀ x, Tendsto (fun n => (p n).eval x) atTop (𝓝 (q.eval x)) := by
    intro x
    have hrw : ∀ P : ℝ[X], P.natDegree ≤ d →
        P.eval x = ∑ j ∈ Finset.range (d + 1), P.coeff j * x ^ j := fun P hP =>
      eval_eq_sum_range' (Nat.lt_succ_of_le hP) x
    rw [hrw q hqd]
    refine (tendsto_finsetSum _ fun j _ => (hconv j).mul_const _).congr fun n => ?_
    rw [hrw _ (hpdeg n)]
  -- sign-change radius at each simple root
  have hη : ∀ y ∈ Z, ∃ η, 0 < η ∧ ∀ ε, 0 < ε → ε < η → q.eval (y - ε) * q.eval (y + ε) < 0 := by
    intro y hy
    have hroot : q.IsRoot y := (mem_roots hq0).1 (Multiset.mem_toFinset.1 hy)
    exact exists_sign_change_of_derivative_ne_zero hroot
      (derivative_eval_ne_zero_of_roots_nodup hq0 hnd hroot)
  choose! η hηpos hηsign using hη
  -- a common radius below every `η` and below half of every separation
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ y ∈ Z, ε < η y) ∧
      ∀ y ∈ Z, ∀ w ∈ Z, y ≠ w → 2 * ε < |y - w| := by
    have hr0 : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    refine ((Filter.eventually_all_finset Z).2 fun y hy =>
      hr0.eventually (gt_mem_nhds (hηpos y hy))).and
      ((Filter.eventually_all_finset Z).2 fun y hy => (Filter.eventually_all_finset Z).2
        fun w hw => ?_)
    by_cases hyw : y = w
    · exact Eventually.of_forall fun _ h => absurd hyw h
    · have hpos : 0 < |y - w| / 2 := by
        have := abs_pos.2 (sub_ne_zero.2 hyw); positivity
      filter_upwards [hr0.eventually (gt_mem_nhds hpos)] with r hr _
      linarith
  obtain ⟨ε, ⟨hεη, hεsep⟩, hεpos⟩ := (hsmall.and self_mem_nhdsWithin).exists
  have hεpos' : 0 < ε := hεpos
  have hev : ∀ᶠ n in atTop, ∀ y ∈ Z, (p n).eval (y - ε) * (p n).eval (y + ε) < 0 :=
    (Filter.eventually_all_finset Z).2 fun y hy =>
      ((heval _).mul (heval _)).eventually_lt_const (hηsign y hy ε hεpos' (hεη y hy))
  filter_upwards [hev] with n hn
  exact splits_of_separated_sign_changes (p n) Z hεpos' (by rw [hZcard]; exact hpdeg n) hn hεsep

/-! ## The shift regime -/

/-- **Gaussian capacity in the shift regime.** For fixed `d` and `s < 1/2`, the backward heat flow
`e^{sD²}` of the normalized Jensen polynomial `J̃^{d,n}` of `Ξ` is real-rooted for all large `n`. -/
theorem eventually_splits_heatOp_xiJensenHermitePolynomial (d : ℕ) {s : ℝ} (hs : s < 1 / 2) :
    ∀ᶠ n in atTop, (heatOp s d (xiJensenHermitePolynomial n d)).Splits := by
  set u := 1 / 2 - s
  have hu : 0 < u := by simp only [u]; linarith
  have hlimit : heatOp s d (hermiteReal d) = hermiteFF (-u) d := by
    rw [hermiteReal_eq_heatOp, heatOp_heatOp (natDegree_X_pow_le d), hermiteFF]
    congr 1; simp only [u]; ring
  set c := Real.sqrt (2 * u)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  set q := hermiteFF (-u) d
  have hqform : q = C (c ^ d) * (hermiteReal d).comp (C c⁻¹ * X + C 0) := hermiteFF_neg_eq d hu
  have hHroots : (hermiteReal d).roots.Nodup ∧ Multiset.card (hermiteReal d).roots = d :=
    realHermite_roots_nodup_card d
  have hHne : hermiteReal d ≠ 0 := realHermite_ne_zero d
  have hqd : q.natDegree ≤ d := (natDegree_heatOp_le _ _ _).trans (natDegree_X_pow_le d)
  have hqcoeff : q.coeff d = 1 := coeff_hermiteFF_self _ d
  have hq0 : q ≠ 0 := fun h0 => by rw [h0, coeff_zero] at hqcoeff; exact zero_ne_one hqcoeff
  have hmapnd : ((hermiteReal d).roots.map fun y => c * y).Nodup :=
    hHroots.1.map fun a b h => mul_left_cancel₀ hc.ne' h
  have hsub : ((hermiteReal d).roots.map fun y => c * y) ≤ q.roots := by
    rw [Multiset.le_iff_subset hmapnd]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
    rw [mem_roots hq0, IsRoot, hqform]
    have hyr : (hermiteReal d).eval y = 0 := (mem_roots hHne).1 hy
    simp [eval_comp, ← mul_assoc, inv_mul_cancel₀ hc.ne', hyr]
  have heq : ((hermiteReal d).roots.map fun y => c * y) = q.roots :=
    Multiset.eq_of_le_of_card_le hsub (by
      rw [Multiset.card_map, hHroots.2]; exact (Polynomial.card_roots' q).trans hqd)
  have hqnd : q.roots.Nodup := heq ▸ hmapnd
  have hqcard : Multiset.card q.roots = d := by rw [← heq, Multiset.card_map, hHroots.2]
  refine eventually_splits_of_tendsto_coeff hq0 hqd hqnd hqcard
    (fun n => (natDegree_heatOp_le _ _ _).trans (natDegree_xiJensenHermitePolynomial_le n d))
    fun j => ?_
  rw [show q = heatOp s d (hermiteReal d) from hlimit.symm, coeff_heatOp]
  simp_rw [coeff_heatOp]
  exact tendsto_finsetSum _ fun k _ =>
    (tendsto_xiJensenHermitePolynomial_coeff d (j + 2 * k)).const_mul _


/-- The same statement for the actual shifted Jensen polynomials `J^{d,n}` of `Ξ`: backward heat by
any fraction `s < 1/2` of the Hermite scale `(δ(n)/A(n))²` keeps them real-rooted for large `n`. -/
theorem eventually_splits_heatOp_jensenPoly_xiJensenCoeff (d : ℕ) {s : ℝ} (hs : s < 1 / 2) :
    ∀ᶠ n in atTop, (heatOp (s * (xiJensenDelta n / xiJensenScale n) ^ 2) d
      (GaloisForLFunctions.SignAlternation.jensenPoly xiJensenCoeff d n)).Splits := by
  filter_upwards [eventually_splits_heatOp_xiJensenHermitePolynomial d hs] with n hn
  have hγ := (xiJensenCoeff_pos n).ne'
  have hδ := (xiJensenDelta_pos n).ne'
  have hA := (xiJensenScale_pos n).ne'
  have hL : (C ((xiJensenScale n)⁻¹) * (C (xiJensenDelta n) * X - 1) : ℝ[X]) =
      C (xiJensenDelta n / xiJensenScale n) * X + C (-(xiJensenScale n)⁻¹) := by
    simp only [div_eq_inv_mul, map_mul, map_neg]; ring
  rw [xiJensenHermitePolynomial, hL, heatOp_C_mul, heatOp_comp_affine] at hn
  have hcomp := (splits_mul_iff_right
    (C_ne_zero.mpr (inv_ne_zero (mul_ne_zero hγ (pow_ne_zero d hδ))))
    (Polynomial.Splits.C _)).mp hn
  exact (splits_iff_comp_splits_of_natDegree_eq_one (by
    rw [natDegree_add_C, natDegree_C_mul_X _ (div_ne_zero hδ hA)])).mpr hcomp

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_splits_heatOp_xiJensenHermitePolynomial
#print axioms FiniteFreeProbability.splits_heatOp_of_le
#print axioms FiniteFreeProbability.eventually_splits_heatOp_jensenPoly_xiJensenCoeff
