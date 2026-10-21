import GaloisForLFunctions.TransHorizonIncidenceMechanics.CubicMomentsPinTheParityOfOddRows
import GaloisForLFunctions.TransHorizonIncidenceMechanics.LocalEulerFactorsAndPronicDilationContraction

/-!
# The even flip is the Fermi transform of the even part

For a horizon-`N` row `c` the **even flip** `c^♭ = scaledSelbergRow N c ε₂` changes the sign of the
Selberg coordinates at every even modulus, `ε₂(q) = -1` for `2 ∣ q`.

**Invisible to every translated moment.** If the coordinates vanish off the squarefree moduli, every
zero-product tuple of response frequencies carries an even number of frequencies of even order: raise
the relation `Π ζ_i = 1` to the odd power `M = Π_i oddpart(ord ζ_i)`; a frequency of squarefree even
order `2e'` goes to `(ζ^{e'})^{M/e'} = -1`, one of odd order to `1`, so `(-1)^{#even} = 1`. By the BVI
sign visibility law the translated moments of `c` and `c^♭` agree at every degree and every shift.

**The Fermi transform.** If `c` is supported on `[1, N]` and vanishes on multiples of four (the
four-free class of the actual PM cofactor rows), Ramanujan inversion gives the row identity

`c^♭(d) = c(d) + c(2d)` for odd `d`,   `c^♭(d) = -c(d)` for even `d`,

that is `c^♭ = c + c_e ⋆ (δ₁ - 2δ₂)` with the even part `c_e(d) = 1_{odd}(d) c(2d)`: the local factor
`1 - 2·2^{-s}` of the Fermi cells `2⌊n/2d⌋ - ⌊n/d⌋`, whose zero lies right of the critical line. The
mean is unchanged, and the pronic dilation contraction gives

`|‖A_{c^♭}‖ - ‖A_c‖| ≤ (1 + √2) ‖A_{c_e}‖ + 2 |m_e|`.

So the only sign twist of a squarefree row that no additive observable of any degree can see costs at
most the receiver of its even part, read through the Fermi trace.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The even sign `ε₂(q) = -1` for even `q`, `1` for odd `q`. -/
def evenSign (q : ℕ) : ℝ := if 2 ∣ q then -1 else 1

theorem evenSign_mul_self (q : ℕ) : evenSign q * evenSign q = 1 := by
  unfold evenSign; split_ifs <;> norm_num

/-- The even flip of a horizon-`N` row. -/
def evenFlipRow (N : ℕ) (c : ℕ → ℝ) : ℕ → ℝ := scaledSelbergRow N c evenSign

/-- The even part `c_e(d) = 1_{odd}(d) c(2d)`. -/
def evenPartWeight (c : ℕ → ℝ) (d : ℕ) : ℝ := if d % 2 = 1 then c (2 * d) else 0

/-! ### Invisibility at every degree -/

/-- The odd part of a squarefree modulus. -/
private def sqfOddPart (e : ℕ) : ℕ := if 2 ∣ e then e / 2 else e

private theorem sqfOddPart_odd {e : ℕ} (he : Squarefree e) (he0 : e ≠ 0) : Odd (sqfOddPart e) := by
  unfold sqfOddPart
  split_ifs with h2
  · obtain ⟨f, rfl⟩ := h2
    rw [Nat.mul_div_cancel_left f (by norm_num)]
    rcases Nat.even_or_odd f with hf | hf
    · exfalso
      obtain ⟨g, rfl⟩ := hf
      have : (2 * 2) ∣ 2 * (g + g) := ⟨g, by ring⟩
      exact absurd (he 2 (by simpa [mul_comm, two_mul] using this)) (by decide)
    · exact hf
  · exact Nat.odd_iff.mpr (by omega)

/-- A frequency of squarefree order `e` raised to an odd multiple `M` of the odd part of `e` is the
even sign `ε₂(e)`. -/
private theorem evenSign_eq_pow {ζ : ℂ} {M : ℕ} (hpos : 0 < orderOf ζ) (hM : Odd M) (hdvd : sqfOddPart (orderOf ζ) ∣ M) :
    ((evenSign (orderOf ζ) : ℝ) : ℂ) = ζ ^ M := by
  unfold evenSign
  unfold sqfOddPart at hdvd
  split_ifs with h2
  · rw [if_pos h2] at hdvd
    obtain ⟨e', he'⟩ := h2
    have he'0 : 0 < e' := by omega
    have hdiv : orderOf ζ / 2 = e' := by rw [he']; omega
    rw [hdiv] at hdvd
    obtain ⟨t, rfl⟩ := hdvd
    have ht : Odd t := (Nat.odd_mul.mp hM).2
    have hsq2 : ζ ^ e' * ζ ^ e' = 1 := by
      rw [← pow_add, show e' + e' = orderOf ζ by omega, pow_orderOf_eq_one]
    have hne : ζ ^ e' ≠ 1 := pow_ne_one_of_lt_orderOf he'0.ne' (by omega)
    have hm1 : ζ ^ e' = -1 := (mul_self_eq_one_iff.mp hsq2).resolve_left hne
    rw [pow_mul, hm1, ht.neg_one_pow]
    push_cast; ring
  · rw [if_neg h2] at hdvd
    obtain ⟨t, rfl⟩ := hdvd
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
    push_cast; ring

/-- **The even flip is invisible to every translated moment** of a squarefree-supported row. -/
theorem translatedMoment_evenFlipRow (N : ℕ) (c : ℕ → ℝ)
    (hsq : ∀ e, ¬ Squarefree e → selbergMultiplesCoord N c e = 0) {m : ℕ} (v : Fin m → ℕ) :
    SieveMoments.translatedMoment N (evenFlipRow N c) v = SieveMoments.translatedMoment N c v := by
  refine (translatedMoment_scaled_eq_iff N c evenSign m).mpr (fun ζ hζ hprod => ?_) v
  by_cases hY : ∃ i, selbergMultiplesCoord N c (orderOf (ζ i)) = 0
  · obtain ⟨i, hi⟩ := hY
    rw [prod_eq_zero (mem_univ i) hi, zero_mul]
  · push Not at hY
    have hsqf : ∀ i, Squarefree (orderOf (ζ i)) := fun i => by
      by_contra h; exact hY i (hsq _ h)
    have hmem : ∀ i, orderOf (ζ i) ∈ Icc 1 N := fun i =>
      orderOf_mem_Icc_of_mem_responseRoots ((Fintype.mem_piFinset.mp hζ) i)
    have hpos : ∀ i, 0 < orderOf (ζ i) := fun i => (mem_Icc.mp (hmem i)).1
    set M := ∏ i, sqfOddPart (orderOf (ζ i))
    have hModd : Odd M := by
      refine prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun i _ => ?_
      exact sqfOddPart_odd (hsqf i) (hpos i).ne'
    have hterm : ∀ i, ((evenSign (orderOf (ζ i)) : ℝ) : ℂ) = ζ i ^ M := fun i =>
      evenSign_eq_pow (hpos i) hModd (dvd_prod_of_mem _ (mem_univ i))
    have hone : ∏ i, evenSign (orderOf (ζ i)) = 1 := by
      have h : ((∏ i, evenSign (orderOf (ζ i)) : ℝ) : ℂ) = 1 := by
        rw [Complex.ofReal_prod]
        simp_rw [hterm]
        rw [prod_pow, hprod, one_pow]
      exact_mod_cast h
    rw [hone, sub_self, mul_zero]

/-! ### The Fermi transform -/

/-- Coordinates of a four-free row vanish at multiples of four. -/
private theorem selbergMultiplesCoord_eq_zero_of_four_dvd {N e : ℕ} {c : ℕ → ℝ}
    (h4 : ∀ d, 4 ∣ d → c d = 0) (he : 4 ∣ e) : selbergMultiplesCoord N c e = 0 := by
  unfold selbergMultiplesCoord
  refine sum_eq_zero fun d hd => ?_
  rw [h4 d (dvd_trans he (mem_filter.mp hd).2), zero_div]

/-- **The row identity of the even flip.** For a four-free row supported on `[1, N]`,
`c^♭ = c + c_e ⋆ (δ₁ - 2δ₂)`. -/
theorem evenFlipRow_eq (N : ℕ) (c : ℕ → ℝ) (hsupp : ∀ d, N < d → c d = 0)
    (h4 : ∀ d, 4 ∣ d → c d = 0) :
    evenFlipRow N c = fun d => c d + localFactorWeight (evenPartWeight c) 2 2 d := by
  funext d
  have hc0 : c 0 = 0 := h4 0 (dvd_zero 4)
  set Y := selbergMultiplesCoord N c
  have hflip : evenFlipRow N c d = (d : ℝ) * ∑ m ∈ Icc 1 (N / d), (moebius m : ℝ) * (evenSign (d * m) * Y (d * m)) := by
    unfold evenFlipRow scaledSelbergRow RHTower.pmRamanujanResidueCoeff; rfl
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · rw [hflip]; simp [localFactorWeight, evenPartWeight, hc0]
  by_cases hdN : N < d
  · -- beyond the horizon both sides vanish
    have h1 : c d = 0 := hsupp d hdN
    have h2 : evenPartWeight c d = 0 := by
      unfold evenPartWeight; split_ifs
      · exact hsupp _ (by omega)
      · rfl
    have h3 : (if 2 ∣ d then evenPartWeight c (d / 2) else 0) = 0 := by
      split_ifs with h
      · obtain ⟨k, rfl⟩ := h
        unfold evenPartWeight
        rw [Nat.mul_div_cancel_left k two_pos]
        split_ifs
        · exact hsupp _ (by omega)
        · rfl
      · rfl
    have hempty : Icc 1 (N / d) = ∅ := Finset.Icc_eq_empty (by rw [Nat.div_eq_of_lt hdN]; omega)
    rw [hflip, hempty, sum_empty, mul_zero]
    simp only [localFactorWeight, h1, h2, h3]
    ring
  have hdmem : d ∈ Icc 1 N := mem_Icc.mpr ⟨hd0, not_lt.mp hdN⟩
  have hinv : c d = (d : ℝ) * ∑ m ∈ Icc 1 (N / d), (moebius m : ℝ) * Y (d * m) :=
    sieveRow_eq_moebius_selbergMultiplesCoord hdmem c
  by_cases h2d : 2 ∣ d
  · -- even `d`: every coordinate flips
    have hsign : ∀ m, evenSign (d * m) = -1 := fun m => by
      simp [evenSign, dvd_mul_of_dvd_left h2d m]
    have hneg : evenFlipRow N c d = -c d := by
      rw [hflip, hinv]
      simp_rw [hsign, neg_one_mul, mul_neg, sum_neg_distrib, mul_neg]
    rw [hneg]
    obtain ⟨k, rfl⟩ := h2d
    simp only [localFactorWeight, evenPartWeight, if_pos (dvd_mul_right 2 k),
      Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
    rw [if_neg (by omega)]
    by_cases hk : k % 2 = 1
    · rw [if_pos hk]; ring
    · have hk2 : 2 ∣ k := by omega
      obtain ⟨j, rfl⟩ := hk2
      rw [if_neg hk, h4 (2 * (2 * j)) ⟨j, by ring⟩]
      ring
  · -- odd `d`: the even cofactors pass the weight to `2d`
    have hsign : ∀ m, evenSign (d * m) = 1 - 2 * (if 2 ∣ m then 1 else 0) := fun m => by
      unfold evenSign
      by_cases hm : 2 ∣ m
      · rw [if_pos (dvd_mul_of_dvd_right hm d), if_pos hm]; ring
      · rw [if_neg (fun h => ((Nat.Prime.dvd_mul Nat.prime_two).mp h).elim h2d hm), if_neg hm]
        ring
    have hsum : ∑ m ∈ Icc 1 (N / d), (moebius m : ℝ) * (evenSign (d * m) * Y (d * m)) =
        ∑ m ∈ Icc 1 (N / d), (moebius m : ℝ) * Y (d * m) -
          2 * ∑ m ∈ (Icc 1 (N / d)).filter (2 ∣ ·), (moebius m : ℝ) * Y (d * m) := by
      rw [sum_filter, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun m _ => ?_
      rw [hsign]; split_ifs <;> ring
    have heven : ∑ m ∈ (Icc 1 (N / d)).filter (2 ∣ ·), (moebius m : ℝ) * Y (d * m) =
        -∑ m ∈ Icc 1 (N / d / 2), (moebius m : ℝ) * Y (2 * d * m) := by
      rw [RHTower.sum_Icc_filter_dvd_reindex 2 (N / d) two_pos, ← sum_neg_distrib]
      refine sum_congr rfl fun m _ => ?_
      rw [show d * (2 * m) = 2 * d * m by ring]
      by_cases hm : 2 ∣ m
      · have hY0 : Y (2 * d * m) = 0 := selbergMultiplesCoord_eq_zero_of_four_dvd h4
          (by obtain ⟨k, rfl⟩ := hm; exact ⟨d * k, by ring⟩)
        rw [hY0]; ring
      · have hmu : (moebius (2 * m) : ℝ) = -(moebius m : ℝ) := by
          have h := RHTower.Sieve.moebius_prime_mul (e := m) Nat.prime_two
          rw [if_neg hm] at h
          exact_mod_cast h
        rw [hmu]; ring
    have hc2d : c (2 * d) =
        ((2 * d : ℕ) : ℝ) * ∑ m ∈ Icc 1 (N / d / 2), (moebius m : ℝ) * Y (2 * d * m) := by
      by_cases h2dN : 2 * d ≤ N
      · rw [sieveRow_eq_moebius_selbergMultiplesCoord (mem_Icc.mpr ⟨by omega, h2dN⟩) c,
          Nat.div_div_eq_div_mul, mul_comm d 2]
      · have h0 : N / d / 2 = 0 := by
          rw [Nat.div_div_eq_div_mul]; exact Nat.div_eq_of_lt (by omega)
        rw [hsupp _ (by omega), h0, Finset.Icc_eq_empty (by omega), sum_empty, mul_zero]
    rw [hflip, hsum, mul_sub, ← hinv, heven]
    simp only [localFactorWeight, evenPartWeight, if_neg h2d, if_pos (show d % 2 = 1 by omega)]
    rw [hc2d]
    push_cast
    ring

/-- The receiver prefix is additive in the weight and the mean. -/
theorem weightCenteredPrefix_add (c g : ℕ → ℝ) (m m' : ℝ) (n : ℕ) :
    weightCenteredPrefix (fun d => c d + g d) (m + m') n =
      weightCenteredPrefix c m n + weightCenteredPrefix g m' n := by
  unfold weightCenteredPrefix
  simp only [sum_add_distrib]
  ring

/-- **The even flip costs at most the Fermi transform of the even part.** For a four-free row
supported on `[1, N]` and any mean `m_e` for the even part:
`‖A_{c^♭}‖ ≤ ‖A_c‖ + (1 + √2)‖A_{c_e}‖ + 2|m_e|` and `‖A_c‖ ≤ ‖A_{c^♭}‖ + (1 + √2)‖A_{c_e}‖ + 2|m_e|`,
both receivers read with the horizon mean `Y_N(1)`. -/
theorem pronicNorm_evenFlipRow_sub_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (hsupp : ∀ d, N < d → c d = 0)
    (h4 : ∀ d, 4 ∣ d → c d = 0) (me : ℝ) (T : ℕ) :
    |pronicNorm (weightCenteredPrefix (evenFlipRow N c)
        (selbergMultiplesCoord N (evenFlipRow N c) 1)) T -
      pronicNorm (weightCenteredPrefix c (selbergMultiplesCoord N c 1)) T| ≤
      (1 + Real.sqrt 2) * pronicNorm (weightCenteredPrefix (evenPartWeight c) me) T + 2 * |me| := by
  have hmean : selbergMultiplesCoord N (evenFlipRow N c) 1 = selbergMultiplesCoord N c 1 := by
    rw [evenFlipRow, selbergMultiplesCoord_scaledSelbergRow _ _ (mem_Icc.mpr ⟨le_refl 1, hN⟩)]
    simp [evenSign]
  set m := selbergMultiplesCoord N c 1
  set g := localFactorWeight (evenPartWeight c) 2 2
  have hA : weightCenteredPrefix (evenFlipRow N c) m =
      fun n => weightCenteredPrefix c m n + weightCenteredPrefix g (me - 2 * (me / 2)) n := by
    funext n
    rw [evenFlipRow_eq N c hsupp h4, ← weightCenteredPrefix_add]
    congr 1; ring
  have hfermi := pronicNorm_localFactor_le (evenPartWeight c) me (by norm_num : 1 ≤ 2) 2 T
  have hsqrt : (1 + |(2 : ℝ)| * ((2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) = 1 + Real.sqrt 2 := by
    rw [abs_of_pos two_pos]
    have h2 : ((2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 2)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]; norm_num
    rw [h2]
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs0 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    linarith
  rw [hsqrt, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)] at hfermi
  rw [hmean, hA]
  set F := pronicNorm (weightCenteredPrefix g (me - 2 * (me / 2))) T
  have h1 := pronicNorm_add_le (weightCenteredPrefix c m) (weightCenteredPrefix g (me - 2 * (me / 2))) T
  have h2 : pronicNorm (weightCenteredPrefix c m) T ≤
      pronicNorm (fun n => weightCenteredPrefix c m n + weightCenteredPrefix g (me - 2 * (me / 2)) n) T +
        F := by
    have h := pronicNorm_add_le
      (fun n => weightCenteredPrefix c m n + weightCenteredPrefix g (me - 2 * (me / 2)) n)
      (fun n => (-1) * weightCenteredPrefix g (me - 2 * (me / 2)) n) T
    rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h
    convert h using 2
    funext n; ring
  rw [abs_le]
  constructor <;> linarith

/-- **The even flip preserves the growth class when the even part is paid.** If the even parts of a
family of four-free horizon rows have uniformly bounded receivers, the even flips have uniformly
bounded receivers iff the rows do. -/
theorem bounded_horizonPronicEnergy_evenFlipRow_iff (c : ℕ → ℕ → ℝ)
    (hsupp : ∀ N d, N < d → c N d = 0) (h4 : ∀ N d, 4 ∣ d → c N d = 0) (me : ℕ → ℝ)
    (heven : ∃ B, ∀ N T, pronicNorm (weightCenteredPrefix (evenPartWeight (c N)) (me N)) T ≤ B ∧
      |me N| ≤ B) :
    (∃ B, ∀ N, 1 ≤ N → ∀ T, horizonPronicEnergy N (c N) T ≤ B) ↔
      (∃ B, ∀ N, 1 ≤ N → ∀ T, horizonPronicEnergy N (evenFlipRow N (c N)) T ≤ B) := by
  obtain ⟨B, hB⟩ := heven
  set K := (1 + Real.sqrt 2) * B + 2 * B
  have hdiff : ∀ N, 1 ≤ N → ∀ T,
      |pronicNorm (weightCenteredPrefix (evenFlipRow N (c N))
          (selbergMultiplesCoord N (evenFlipRow N (c N)) 1)) T -
        pronicNorm (weightCenteredPrefix (c N) (selbergMultiplesCoord N (c N) 1)) T| ≤ K := by
    intro N hN T
    have h := pronicNorm_evenFlipRow_sub_le hN (c N) (hsupp N) (h4 N) (me N) T
    have hb := hB N T
    have hs : 0 ≤ 1 + Real.sqrt 2 := by positivity
    calc _ ≤ _ := h
      _ ≤ K := by simp only [K]; nlinarith [hb.1, hb.2]
  unfold horizonPronicEnergy
  simp_rw [weightPronicEnergy_eq_sq_pronicNorm]
  constructor
  · rintro ⟨B', hB'⟩
    refine ⟨(Real.sqrt (max B' 0) + K) ^ 2, fun N hN T => ?_⟩
    have hN' := Real.le_sqrt_of_sq_le ((hB' N hN T).trans (le_max_left B' 0))
    exact pow_le_pow_left₀ (pronicNorm_nonneg _ _) (by linarith [(abs_le.mp (hdiff N hN T)).2]) 2
  · rintro ⟨B', hB'⟩
    refine ⟨(Real.sqrt (max B' 0) + K) ^ 2, fun N hN T => ?_⟩
    have hN' := Real.le_sqrt_of_sq_le ((hB' N hN T).trans (le_max_left B' 0))
    exact pow_le_pow_left₀ (pronicNorm_nonneg _ _) (by linarith [(abs_le.mp (hdiff N hN T)).1]) 2

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
