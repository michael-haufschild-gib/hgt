import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace
import GaloisForLFunctions.HTGeometry.OrbitInductionEssentialization
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic-order splitting of the prime gas

At energy log n, record the order a of a residue modulo n and the index b = n/a.
Compression onto the normalized uniform vector in each order class gives the
amplitude √φ(a) times the original heat multiplier. Distinct energy shells
land on disjoint pairs in the two-copy occupation basis.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

abbrev PairGas := lp (fun _ : ℕ+ × ℕ+ => ℂ) 2

/-- Amplitude in an order class, before the input coefficient is applied. -/
def channel (s : ℂ) (n : ℕ+) (a : ℕ) : ℂ :=
  (Real.sqrt a.totient : ℂ) * heat s n

/-- Two-copy wave function in the ordered factor basis. -/
def split (s : ℂ) (f : ℕ+ → ℂ) (x : ℕ+ × ℕ+) : ℂ :=
  channel s (x.1 * x.2) x.1 * f (x.1 * x.2)

/-- The squared multiplicity factor counts the residues of the specified order. -/
theorem channel_order_count (a b : ℕ+) :
    (Finset.univ.filter (fun j : ZMod ((a * b : ℕ+) : ℕ) => addOrderOf j = (a : ℕ))).card =
      (a : ℕ).totient := by
  apply IsAddCyclic.card_addOrderOf_eq_totient
  rw [ZMod.card, PNat.mul_coe]
  exact dvd_mul_right _ _

/-- Projection of the uniform residue wave onto the normalized constant vector of
one order class gives exactly the corresponding two-copy coefficient. -/
theorem uniform_order_projection (s : ℂ) (a b : ℕ+) :
    (∑ _j ∈ Finset.univ.filter (fun j : ZMod ((a * b : ℕ+) : ℕ) => addOrderOf j = (a : ℕ)),
      heat s (a * b) / (Real.sqrt (a : ℕ).totient : ℂ)) = channel s (a * b) a := by
  rw [Finset.sum_const, nsmul_eq_mul, channel_order_count, channel]
  have hpos : 0 < ((a : ℕ).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr a.pos
  have hn : (Real.sqrt (a : ℕ).totient : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hpos).ne'
  have hs : (Real.sqrt (a : ℕ).totient : ℂ) ^ 2 = (a : ℕ).totient := by
    exact_mod_cast Real.sq_sqrt hpos.le
  rw [← hs, div_eq_mul_inv]
  field_simp [hn]

theorem channel_norm_sq (s : ℂ) (n : ℕ+) (a : ℕ) :
    ‖channel s n a‖ ^ 2 = a.totient * ‖heat s n‖ ^ 2 := by
  rw [channel, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Residues at coprime orders combine independently. -/
theorem channel_coprime_mul (s : ℂ) (n m : ℕ+) {a b : ℕ} (h : a.Coprime b) :
    channel s (n * m) (a * b) = channel s n a * channel s m b := by
  simp only [channel, Nat.totient_mul h, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
    Complex.ofReal_mul, heat_mul]
  ring

/-- The shell Gram multiplier includes both propagation parameters and the exact degeneracy. -/
theorem shell_pairing (w s : ℂ) (n : ℕ+) :
    ∑ a ∈ (n : ℕ).divisors, conj (channel w n a) * channel s n a =
      (n : ℕ) * heat (conj w + s) n := by
  have hc : conj (heat w n) = heat (conj w) n := by
    simp [heat, ← Complex.exp_conj]
  have hc' (a : ℕ) : conj (channel w n a) * channel s n a =
      (a.totient : ℂ) * heat (conj w + s) n := by
    simp only [channel, map_mul, Complex.conj_ofReal, hc, heat_add]
    have hsq : (Real.sqrt a.totient : ℂ) ^ 2 = a.totient := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg a.totient)
    linear_combination (heat (conj w) n * heat s n) * hsq
  simp_rw [hc']
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_totient]

/-- The adjoint pairing of the complementary channels is exactly one on every shell. -/
theorem reflected_shell_pairing (s : ℂ) (n : ℕ+) :
    ∑ a ∈ (n : ℕ).divisors, conj (channel (1 - conj s) n a) * channel s n a = 1 := by
  rw [shell_pairing]
  simp only [map_sub, map_one, Complex.conj_conj, sub_add_cancel, heat_eq_cpow,
    Complex.cpow_neg, Complex.cpow_one]
  exact mul_inv_cancel₀ (by exact_mod_cast n.ne_zero)

/-- Exact squared norm multiplier of the split on a shell. -/
def shellMass (s : ℂ) (n : ℕ+) : ℝ := Real.exp ((1 - 2 * s.re) * energy n)

theorem shellMass_eq (s : ℂ) (n : ℕ+) :
    shellMass s n = (n : ℕ) * ‖heat s n‖ ^ 2 := by
  rw [shellMass, norm_heat, sq, ← Real.exp_add,
    ← Real.exp_log (show 0 < ((n : ℕ) : ℝ) by exact_mod_cast n.pos), ← Real.exp_add]
  congr 1
  unfold energy
  ring

private theorem shell_sum (s : ℂ) (f : ℕ+ → ℂ) (n : ℕ+) :
    (∑' d : (n : ℕ).divisorsAntidiagonal,
      ‖split s f (sigmaAntidiagonalEquivProd ⟨n, d⟩)‖ ^ 2) =
      shellMass s n * ‖f n‖ ^ 2 := by
  have hprod (d : (n : ℕ).divisorsAntidiagonal) :
      (divisorsAntidiagonalFactors n d).1 * (divisorsAntidiagonalFactors n d).2 = n :=
    PNat.coe_injective (divisorsAntidiagonalFactors_eq d)
  have hterm (d : (n : ℕ).divisorsAntidiagonal) :
      ‖split s f (sigmaAntidiagonalEquivProd ⟨n, d⟩)‖ ^ 2 =
      (d.val.1.totient : ℝ) * (‖heat s n‖ ^ 2 * ‖f n‖ ^ 2) := by
    let x := divisorsAntidiagonalFactors n d
    change ‖channel s (x.1 * x.2) d.val.1 * f (x.1 * x.2)‖ ^ 2 = _
    have hx : x.1 * x.2 = n := hprod d
    rw [hx, norm_mul, mul_pow, channel_norm_sq, mul_assoc]
  simp_rw [hterm]
  rw [tsum_fintype, ← Finset.sum_mul, ← Nat.cast_sum, Finset.univ_eq_attach,
    (n : ℕ).divisorsAntidiagonal.sum_attach (fun d => d.1.totient),
    Nat.sum_divisorsAntidiagonal (fun a _ => a.totient), Nat.sum_totient,
    shellMass_eq, mul_assoc]

/-- Exact domain and norm of the split, including waves on which it is unbounded. -/
theorem split_hasSum_iff (s : ℂ) (f : ℕ+ → ℂ) (r : ℝ) :
    HasSum (fun x => ‖split s f x‖ ^ 2) r ↔
      HasSum (fun n => shellMass s n * ‖f n‖ ^ 2) r := by
  rw [← sigmaAntidiagonalEquivProd.hasSum_iff]
  have hrow (n : ℕ+) := (hasSum_fintype
    (fun d : (n : ℕ).divisorsAntidiagonal =>
      ‖split s f (sigmaAntidiagonalEquivProd ⟨n, d⟩)‖ ^ 2)).summable.hasSum
  constructor
  · intro h
    exact h.sigma fun n => (shell_sum s f n) ▸ hrow n
  · intro h
    have hs : Summable ((fun x => ‖split s f x‖ ^ 2) ∘ sigmaAntidiagonalEquivProd) := by
      apply (summable_sigma_of_nonneg fun _ => sq_nonneg _).2
      exact ⟨fun n => (hrow n).summable, by simpa only [Function.comp_apply, shell_sum] using h.summable⟩
    rw [← h.tsum_eq]
    convert hs.hasSum using 1
    rw [hs.tsum_sigma]
    simp only [Function.comp_apply, shell_sum]

private theorem onLine_mass {s : ℂ} (hs : s.re = 1 / 2) (n : ℕ+) : shellMass s n = 1 := by
  simp [shellMass, hs]

/-- On the critical line the cyclic-order split extends to the entire Hilbert space. -/
def splitIsometry (s : {z : ℂ // z.re = 1 / 2}) : Gas →ₗᵢ[ℂ] PairGas := by
  have hnorm (f : Gas) : HasSum (fun x => ‖split s.val f x‖ ^ 2) (‖f‖ ^ 2) := by
    apply (split_hasSum_iff ..).2
    simpa only [onLine_mass s.2, one_mul, lp_norm_sq_eq_tsum] using (lp_summable_norm_sq f).hasSum
  let image (f : Gas) : PairGas := ⟨split s.val f, memℓp_gen (by
    simpa using (hnorm f).summable)⟩
  exact
    { toFun := image
      map_add' := fun f g => Subtype.ext (funext fun x => mul_add _ _ _)
      map_smul' := fun c f => Subtype.ext (funext fun x => by
        change _ * (c * _) = c * (_ * _)
        ring)
      norm_map' := fun f => by
        change ‖image f‖ = ‖f‖
        have he : ‖image f‖ ^ 2 = ‖f‖ ^ 2 := (lp_norm_sq_eq_tsum (image f)).trans (hnorm f).tsum_eq
        nlinarith only [he, norm_nonneg (image f), norm_nonneg f] }

/-- The two-copy formula admits a linear isometry precisely on the critical line. -/
theorem split_isometric_iff (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔ s.re = 1 / 2 := by
  constructor
  · rintro ⟨T, hT⟩
    let e : Gas := lp.single 2 (2 : ℕ+) (1 : ℂ)
    have h : HasSum (fun x => ‖split s e x‖ ^ 2) (‖e‖ ^ 2) := by
      simp_rw [← hT]
      rw [← T.norm_map e, lp_norm_sq_eq_tsum]
      exact (lp_summable_norm_sq (T e)).hasSum
    have hv := ((split_hasSum_iff s e _).1 h).tsum_eq
    rw [tsum_eq_single (2 : ℕ+)] at hv
    · have hm : shellMass s 2 = 1 := by simpa [e, lp.norm_single, lp.single_apply] using hv
      have hz := (Real.exp_eq_one_iff _).1 hm
      have he : 0 < energy 2 := Real.log_pos (by norm_num)
      rcases mul_eq_zero.mp hz with hz | hz
      · linarith
      · exact (he.ne' hz).elim
    · intro n hn
      simp [e, lp.single_apply, Pi.single_eq_of_ne hn]
  · intro hs
    exact ⟨splitIsometry ⟨s, hs⟩, fun _ _ => rfl⟩

#print axioms channel_order_count
#print axioms uniform_order_projection
#print axioms channel_coprime_mul
#print axioms reflected_shell_pairing
#print axioms split_hasSum_iff
#print axioms split_isometric_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
