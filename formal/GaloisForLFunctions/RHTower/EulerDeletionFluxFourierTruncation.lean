import GaloisForLFunctions.RHTower.EulerDeletionFluxWeightReplacement
import GaloisForLFunctions.RHTower.PoissonSummationPiecewise

/-!
# Finite-frequency approximation of the complete Möbius divisor flux

The second-Bernoulli cosine series approximates each modular primitive with
error at most `e / (π² Q)` after frequency Q. Summing the literal Möbius
coefficients and every divisor-channel time gives aggregate error at most
`(N+1) harmonic(N) / (π² Q)`. Both the original and truncated channel series
are absolutely convergent. Frequencies through N+1 therefore leave only a
logarithmic error in the complete flux.

This controls frequency truncation. It does not bound the retained signed
arithmetic sum. No chronological cutoff or period average replaces the tail.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower.DeletionFlux

private def fourierAtom (e k m : ℕ) : ℝ :=
  (e : ℝ)/(2*Real.pi^(2 : ℕ)) *
    ((Real.cos (2*Real.pi*m*((k : ℝ)/e))-1)/(m : ℝ)^(2 : ℕ))

/-- The modular primitive with Bernoulli frequencies one through Q retained. -/
def fourierPrimitive (Q e k : ℕ) : ℝ :=
  ∑ m ∈ range (Q+1), fourierAtom e k m

/-- Actual Möbius coefficients applied to the finite-frequency primitives. -/
def truncatedPrimitive (N Q k : ℕ) : ℝ :=
  ∑ e ∈ Icc 1 N, ((ArithmeticFunction.moebius e : ℤ) : ℝ) * fourierPrimitive Q e k

/-- All divisor-channel times remain present after truncating the Bernoulli frequencies. -/
def truncatedReciprocalFlux (N Q : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    ∑' j : ℕ, truncatedPrimitive N Q (d*(N/d+j+1)) /
      ((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ)

private theorem reciprocal_bound {q : ℕ} (hq : 0 < q) {C : ℝ}
    (hC : 0 ≤ C) (f : ℕ → ℝ)
    (h : ∀ j, |f j| ≤ C / (((q : ℝ)+j)*((q : ℝ)+j+1))) :
    Summable f ∧ |∑' j, f j| ≤ C/q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hb (T : ℕ) : ∑ j ∈ range T, |f j| ≤ C/q := by
    calc _ ≤ ∑ j ∈ range T, C / (((q : ℝ)+j)*((q : ℝ)+j+1)) :=
           sum_le_sum (fun j _ => h j)
         _ = C/q - C/((q : ℝ)+T) := by
           calc _ = ∑ j ∈ range T, (C/((q : ℝ)+j)-C/((q : ℝ)+(j+1 : ℕ))) := by
                  apply sum_congr rfl
                  intro j hj
                  push_cast
                  field_simp
                  ring
                _ = _ := by
                  simpa using sum_range_sub' (fun j : ℕ => C/((q : ℝ)+j)) T
         _ ≤ _ := sub_le_self _ (by positivity)
  have ha : Summable (fun j => |f j|) := summable_of_sum_range_le (fun _ => abs_nonneg _) hb
  refine ⟨summable_abs_iff.mp ha, ?_⟩
  have hlim : (∑' j, |f j|) ≤ C/q :=
    le_of_tendsto ha.hasSum.tendsto_sum_nat (Eventually.of_forall hb)
  have hnorm : Summable (fun j => ‖f j‖) := by simpa only [Real.norm_eq_abs] using ha
  simpa only [Real.norm_eq_abs] using (norm_tsum_le_tsum_norm hnorm).trans hlim

private theorem hasSum_fourierAtom {e : ℕ} (he : 0 < e) (k : ℕ) :
    HasSum (fourierAtom e k) (HTGeometry.centeredModularPrimitive e k) := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have h := ((GaloisForLFunctions.RHTower.hasSum_cos_div_sq ((k : ℝ)/e)).sub
    (GaloisForLFunctions.RHTower.hasSum_cos_div_sq 0)).mul_left ((e : ℝ)/(2*Real.pi^(2 : ℕ)))
  have ht := h.congr_fun (g := fourierAtom e k) (fun m => by
    dsimp only [fourierAtom]
    simp only [mul_zero, Real.cos_zero]
    ring)
  have hv : (e : ℝ)/(2*Real.pi^(2 : ℕ)) *
      (2*Real.pi^(2 : ℕ)*(1/12-GaloisForLFunctions.RHTower.sawPrimitive ((k : ℝ)/e)) -
       2*Real.pi^(2 : ℕ)*(1/12-GaloisForLFunctions.RHTower.sawPrimitive 0)) =
      HTGeometry.centeredModularPrimitive e k := by
    simp only [GaloisForLFunctions.RHTower.sawPrimitive,
      Int.fract_div_natCast_eq_div_natCast_mod, HTGeometry.centeredModularPrimitive]
    norm_num only [Int.fract_zero, zero_pow, sub_zero]
    field_simp
    ring
  rw [hv] at ht
  exact ht

private theorem atom_bound (e k m : ℕ) :
    |fourierAtom e k m| ≤ (e : ℝ)/(Real.pi^(2 : ℕ)*(m : ℝ)^(2 : ℕ)) := by
  have hc : |Real.cos (2*Real.pi*m*((k : ℝ)/e))-1| ≤ 2 :=
    abs_le.mpr ⟨by linarith [Real.neg_one_le_cos (2*Real.pi*m*((k : ℝ)/e))],
      by linarith [Real.cos_le_one (2*Real.pi*m*((k : ℝ)/e))]⟩
  rw [fourierAtom, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (e : ℝ)/(2*Real.pi^(2 : ℕ)))]
  simp only [abs_div, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m)]
  calc _ ≤ (e : ℝ)/(2*Real.pi^(2 : ℕ))*(2/(m : ℝ)^(2 : ℕ)) := by
         exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc (sq_nonneg _))
           (by positivity)
       _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

private theorem primitive_fourier_error {Q e : ℕ} (hQ : 0 < Q) (he : 0 < e) (k : ℕ) :
    |HTGeometry.centeredModularPrimitive e k-fourierPrimitive Q e k| ≤
      (e : ℝ)/(Real.pi^(2 : ℕ)*Q) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hb := reciprocal_bound hQ (C := (e : ℝ)/Real.pi^(2 : ℕ)) (by positivity)
    (fun j => fourierAtom e k (j+(Q+1))) (by
      intro j
      calc _ ≤ (e : ℝ)/(Real.pi^(2 : ℕ)*(j+(Q+1 : ℕ))^(2 : ℕ)) := by
             simpa only [Nat.cast_add] using atom_bound e k (j+(Q+1))
           _ ≤ ((e : ℝ)/Real.pi^(2 : ℕ))/(((Q : ℝ)+j)*((Q : ℝ)+j+1)) := by
             rw [div_div]
             apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
             push_cast
             have h : (0 : ℝ) ≤ (Q : ℝ)+j := by positivity
             nlinarith [sq_pos_of_pos Real.pi_pos])
  have hs := (hasSum_fourierAtom he k).summable.sum_add_tsum_nat_add (Q+1)
  rw [(hasSum_fourierAtom he k).tsum_eq] at hs
  have heq : HTGeometry.centeredModularPrimitive e k-fourierPrimitive Q e k =
      ∑' j : ℕ, fourierAtom e k (j+(Q+1)) := by
    dsimp only [fourierPrimitive]
    linarith
  rw [heq]
  simpa only [div_div] using hb.2

private theorem sum_nat (N : ℕ) :
    (∑ e ∈ Icc 1 N, (e : ℝ)) = (N : ℝ)*(N+1)/2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

private theorem abs_mu_le (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

private theorem source_error {Q : ℕ} (hQ : 0 < Q) (N k : ℕ) :
    |primitive N k-truncatedPrimitive N Q k| ≤
      (N : ℝ)*(N+1)/(2*Real.pi^(2 : ℕ)*Q) := by
  rw [primitive, truncatedPrimitive, ← sum_sub_distrib]
  calc _ ≤ ∑ e ∈ Icc 1 N,
         |((ArithmeticFunction.moebius e : ℤ) : ℝ) *
           (HTGeometry.centeredModularPrimitive e k-fourierPrimitive Q e k)| := by
           simpa only [mul_sub] using abs_sum_le_sum_abs
             (fun e => ((ArithmeticFunction.moebius e : ℤ) : ℝ) *
               HTGeometry.centeredModularPrimitive e k -
               ((ArithmeticFunction.moebius e : ℤ) : ℝ)*fourierPrimitive Q e k) (Icc 1 N)
       _ ≤ ∑ e ∈ Icc 1 N, (e : ℝ)/(Real.pi^(2 : ℕ)*Q) := by
         apply sum_le_sum
         intro e he
         rw [abs_mul]
         have h := primitive_fourier_error hQ (mem_Icc.mp he).1 k
         exact (mul_le_mul (abs_mu_le e) h (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
       _ = _ := by rw [← sum_div, sum_nat]; ring

private theorem channel_error {N Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) (hdN : d ≤ N) :
    Summable (fun j : ℕ => (primitive N (d*(N/d+j+1))-
      truncatedPrimitive N Q (d*(N/d+j+1))) / ((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ)) ∧
    |∑' j : ℕ, (primitive N (d*(N/d+j+1))-
      truncatedPrimitive N Q (d*(N/d+j+1))) / ((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ)| ≤
        (N+1 : ℝ)/(Real.pi^(2 : ℕ)*Q*d) := by
  let B : ℝ := (N : ℝ)*(N+1)/(2*Real.pi^(2 : ℕ)*Q)
  have hN : 0 < N := hd.trans_le hdN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hq : 0 < N/d := Nat.div_pos hdN hd
  have hqR : (0 : ℝ) < (N/d : ℕ) := by exact_mod_cast hq
  have hNq : N ≤ 2*d*(N/d) := by
    have hm := Nat.mod_lt N hd
    have he := Nat.mod_add_div N d
    nlinarith
  have hb := reciprocal_bound hq (C := B/(d : ℝ)^(2 : ℕ)) (by dsimp [B]; positivity)
    (fun j : ℕ => (primitive N (d*(N/d+j+1))-
      truncatedPrimitive N Q (d*(N/d+j+1))) / ((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ)) (by
      intro j
      simp only [abs_div, abs_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ ((d*(N/d+j+1) : ℕ) : ℝ) from Nat.cast_nonneg _)]
      have hi : 1/((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ) ≤
          (1/(d : ℝ)^(2 : ℕ))/((((N/d : ℕ) : ℝ)+j)*(((N/d : ℕ) : ℝ)+j+1)) := by
        rw [div_div]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        push_cast
        have ht : (0 : ℝ) ≤ ((N/d : ℕ) : ℝ)+j := by positivity
        nlinarith [sq_pos_of_pos hdR]
      calc _ ≤ B*(1/((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ)) := by
             simpa only [mul_one_div] using
               div_le_div_of_nonneg_right (source_error hQ N (d*(N/d+j+1)))
                 (sq_nonneg (((d*(N/d+j+1) : ℕ) : ℝ)))
           _ ≤ B*((1/(d : ℝ)^(2 : ℕ))/((((N/d : ℕ) : ℝ)+j)*(((N/d : ℕ) : ℝ)+j+1))) :=
             mul_le_mul_of_nonneg_left hi (by dsimp [B]; positivity)
           _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring)

  refine ⟨hb.1, hb.2.trans ?_⟩
  have hNqR : (N : ℝ) ≤ 2*(d : ℝ)*(N/d : ℕ) := by exact_mod_cast hNq
  dsimp [B]
  apply (div_le_iff₀ hqR).mpr
  field_simp
  nlinarith

private theorem channel_difference {N Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) (hdN : d ≤ N) :
    |(∑' j : ℕ, primitive N (d*(N/d+j+1))/((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ)) -
      ∑' j : ℕ, truncatedPrimitive N Q (d*(N/d+j+1))/((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ)| ≤
        (N+1 : ℝ)/(Real.pi^(2 : ℕ)*Q*d) := by
  have ho := (channels_summable hd hdN).1
  have he := channel_error hQ hd hdN
  have ht : Summable (fun j : ℕ => truncatedPrimitive N Q (d*(N/d+j+1)) /
      ((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ)) := by
    apply (ho.sub he.1).congr
    intro j
    ring
  rw [← ho.tsum_sub ht]
  simpa only [sub_div] using he.2

/-- A finite Bernoulli frequency cutoff has a quantitative error in the complete signed flux. -/
theorem flux_fourier_error (N Q : ℕ) :
    |reciprocalFlux N-truncatedReciprocalFlux N (Q+1)| ≤
      (N+1 : ℝ)*(harmonic N : ℝ)/(Real.pi^(2 : ℕ)*(Q+1)) := by
  rw [reciprocalFlux, truncatedReciprocalFlux, ← sum_sub_distrib]
  calc _ ≤ ∑ d ∈ Icc 1 N,
         |((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ((∑' j : ℕ, primitive N (d*(N/d+j+1))/((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ)) -
           ∑' j : ℕ, truncatedPrimitive N (Q+1) (d*(N/d+j+1))/((d*(N/d+j+1) : ℕ) : ℝ)^(2 : ℕ))| := by
             simpa only [mul_sub] using abs_sum_le_sum_abs _ (Icc 1 N)
       _ ≤ ∑ d ∈ Icc 1 N, (N+1 : ℝ)/(Real.pi^(2 : ℕ)*(Q+1)*d) := by
         apply sum_le_sum
         intro d hd
         rw [abs_mul]
         have h := channel_difference (by omega : 0 < Q+1) (mem_Icc.mp hd).1 (mem_Icc.mp hd).2
         simpa only [one_mul, Nat.cast_add, Nat.cast_one] using
           (mul_le_mul (abs_mu_le d) h (abs_nonneg _) (by norm_num))
       _ = _ := by
         have hh : (harmonic N : ℝ) = ∑ d ∈ Icc 1 N, (1 : ℝ)/d := by
           rw [harmonic_eq_sum_Icc]
           push_cast
           simp only [one_div]
         rw [hh, mul_sum, sum_div]
         apply sum_congr rfl
         intro d hd
         simp only [div_eq_mul_inv, mul_inv_rev]
         ring

/-- Frequencies through N+1 leave at most logarithmic aggregate error, with every time retained. -/
theorem flux_fourier_cutoff_error (N : ℕ) :
    |reciprocalFlux N-truncatedReciprocalFlux N (N+1)| ≤ (harmonic N : ℝ)/Real.pi^(2 : ℕ) := by
  have h := flux_fourier_error N N
  have hN : (N : ℝ)+1 ≠ 0 := by positivity
  convert h using 1
  field_simp

end RHTower.DeletionFlux
