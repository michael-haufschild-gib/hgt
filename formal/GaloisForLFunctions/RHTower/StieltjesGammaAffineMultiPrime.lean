import GaloisForLFunctions.RHTower.StieltjesGammaAffineSinglePrime
import GaloisForLFunctions.RHTower.CoprimeDirichletDivisorProduct

/-!
# The γ-affine structure of the general finite-support Stieltjes constants

For a finite list `ps` of distinct primes and orders `β p ≥ 1` the generalized Stieltjes structure
constant of the multi-index `β` supported on `ps` is the regularized limit

```text
A_β = reg-lim_{N → ∞} ( ∑_{k ≤ N} ∏_{p ∈ ps} v_p(k)^{β p} / k  −  D_β · log N ).
```

Multiplying the single-prime prime-power ladders together (they have coprime supports, so their
Dirichlet convolution has a product divisor sum) realizes `∏_p v_p(k)^{β p}` as a divisor
transform, and the regularization device then gives

```text
A_β = γ · D_β  −  ∑_{p ∈ ps} λ_p · log p,
      D_β = ∏_{p ∈ ps} D_{β p, p},
      λ_p = L_{β p, p} · ∏_{q ≠ p} D_{β q, q},
```

with every `D` and `L` rational.  So `A_β ∈ ℚ·γ ⊕ ⊕_p ℚ·log p`, which is the card's γ-affine
structure theorem in full generality.
-/

open Finset Filter Topology

namespace RHTower
namespace StieltjesGammaAffine

open CoprimeDirichlet RegularizedDivisorHarmonic

noncomputable section

/-- The multi-prime ladder coefficient field, built by iterated coprime convolution. -/
def multiLadder (β : ℕ → ℕ) : List ℕ → (ℕ → ℝ)
  | [] => fun d => if d = 1 then 1 else 0
  | (p :: ps) => dconv (multiLadder β ps) (primePowerLadder p (β p))

@[simp] theorem multiLadder_nil (β : ℕ → ℕ) (d : ℕ) :
    multiLadder β [] d = if d = 1 then 1 else 0 := rfl

@[simp] theorem multiLadder_cons (β : ℕ → ℕ) (p : ℕ) (ps : List ℕ) :
    multiLadder β (p :: ps) = dconv (multiLadder β ps) (primePowerLadder p (β p)) := rfl

theorem multiLadder_zero (β : ℕ → ℕ) (ps : List ℕ) : multiLadder β ps 0 = 0 := by
  induction ps with
  | nil => simp
  | cons p ps _ => simp [multiLadder_cons, dconv]

/-- Every nonzero coefficient of the multi-prime ladder is supported on the listed primes. -/
theorem multiLadder_primeFactors (β : ℕ → ℕ) {ps : List ℕ} (hprime : ∀ q ∈ ps, q.Prime)
    {d : ℕ} (hd : multiLadder β ps d ≠ 0) : ∀ q ∈ d.primeFactors, q ∈ ps := by
  induction ps generalizing d with
  | nil =>
    intro q hq
    have hd1 : d = 1 := by
      by_contra h
      rw [multiLadder_nil, if_neg h] at hd
      exact hd rfl
    rw [hd1] at hq
    simp at hq
  | cons p ps ih =>
    intro q hq
    have hpprime : p.Prime := hprime p (List.mem_cons_self ..)
    rw [multiLadder_cons, dconv] at hd
    obtain ⟨x, hxmem, hxnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
    simp only [Nat.mem_divisorsAntidiagonal] at hxmem
    obtain ⟨hef, hd0⟩ := hxmem
    have hA : multiLadder β ps x.1 ≠ 0 := fun h => hxnz (by rw [h, zero_mul])
    have hB : primePowerLadder p (β p) x.2 ≠ 0 := fun h => hxnz (by rw [h, mul_zero])
    have he0 : x.1 ≠ 0 := by
      intro h; apply hd0; rw [← hef, h, zero_mul]
    have hf0 : x.2 ≠ 0 := by
      intro h; apply hd0; rw [← hef, h, mul_zero]
    have hsplit : d.primeFactors = x.1.primeFactors ∪ x.2.primeFactors := by
      rw [← hef, Nat.primeFactors_mul he0 hf0]
    rw [hsplit, Finset.mem_union] at hq
    rcases hq with hq | hq
    · exact List.mem_cons_of_mem _ (ih (fun r hr => hprime r (List.mem_cons_of_mem _ hr)) hA q hq)
    · obtain ⟨i, hi⟩ := primePowerLadder_support hpprime (β p) (by simpa using hB)
      have hqp : q = p := by
        have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
        have hqdvd : q ∣ x.2 := Nat.dvd_of_mem_primeFactors hq
        rw [← hi] at hqdvd
        exact (Nat.prime_dvd_prime_iff_eq hqprime hpprime).mp (hqprime.dvd_of_dvd_pow hqdvd)
      rw [hqp]
      exact List.mem_cons_self ..

theorem coprimeSupport_multiLadder (β : ℕ → ℕ) {ps : List ℕ} (hprime : ∀ q ∈ ps, q.Prime)
    {p : ℕ} (hp : p.Prime) (hps : p ∉ ps) :
    CoprimeSupport (multiLadder β ps) (primePowerLadder p (β p)) := by
  intro e f he hf
  have he0 : e ≠ 0 := by
    intro h; rw [h, multiLadder_zero] at he; exact he rfl
  have hf0 : f ≠ 0 := by
    intro h; rw [h, primePowerLadder] at hf; simp at hf
  refine (Nat.disjoint_primeFactors he0 hf0).mp ?_
  rw [Finset.disjoint_left]
  intro q hqe hqf
  have hq1 : q ∈ ps := multiLadder_primeFactors β hprime he q hqe
  obtain ⟨i, hi⟩ := primePowerLadder_support hp (β p) (by simpa using hf)
  have hqp : q = p := by
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqf
    have hqdvd : q ∣ f := Nat.dvd_of_mem_primeFactors hqf
    rw [← hi] at hqdvd
    exact (Nat.prime_dvd_prime_iff_eq hqprime hp).mp (hqprime.dvd_of_dvd_pow hqdvd)
  rw [hqp] at hq1
  exact hps hq1

/-- **The multi-prime ladder is a divisor transform of the valuation-power product.** -/
theorem sum_divisors_multiLadder {β : ℕ → ℕ} (hβ : ∀ q, 1 ≤ β q) {ps : List ℕ}
    (hprime : ∀ q ∈ ps, q.Prime) (hnodup : ps.Nodup) {k : ℕ} (hk : k ≠ 0) :
    ∑ d ∈ k.divisors, multiLadder β ps d
      = (ps.map (fun q => ((padicValNat q k : ℕ) : ℝ) ^ β q)).prod := by
  induction ps with
  | nil =>
    simp only [multiLadder_nil, List.map_nil, List.prod_nil]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro d _ hd
      rw [if_neg hd]
    · intro h
      exact absurd (Nat.one_mem_divisors.mpr hk) h
  | cons p ps ih =>
    have hpprime : p.Prime := hprime p (List.mem_cons_self ..)
    have hpsprime : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem _ hq)
    have hpns : p ∉ ps := by
      rw [List.nodup_cons] at hnodup
      exact hnodup.1
    rw [multiLadder_cons,
      sum_divisors_dconv (coprimeSupport_multiLadder β hpsprime hpprime hpns) hk,
      ih hpsprime (by rw [List.nodup_cons] at hnodup; exact hnodup.2),
      sum_divisors_primePowerLadder hpprime (hβ p) hk]
    simp only [List.map_cons, List.prod_cons]
    ring

/-! ### The two regularization hypotheses for the multi-prime ladder -/

theorem summable_logWeight_multiLadder (β : ℕ → ℕ) {ps : List ℕ} (hprime : ∀ q ∈ ps, q.Prime) :
    Summable (logWeight (multiLadder β ps)) := by
  induction ps with
  | nil =>
    refine summable_of_ne_finset_zero (s := ({1} : Finset ℕ)) fun d hd => ?_
    have hd1 : d ≠ 1 := by simpa using hd
    rw [logWeight, multiLadder_nil, if_neg hd1]
    simp
  | cons p ps ih =>
    have hpprime : p.Prime := hprime p (List.mem_cons_self ..)
    have hpsprime : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem _ hq)
    rw [multiLadder_cons]
    exact summable_logWeight_dconv (ih hpsprime) (summable_logWeight_primePowerLadder hpprime _)

theorem logPolyMass_primePowerLadder {p : ℕ} (hp : p.Prime) {β : ℕ} (hβ : 1 ≤ β) :
    LogPolyMass (primePowerLadder p β) ((1 / Real.log p) ^ β) β := by
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  refine ⟨by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.cast_zero]
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) by decide]
    simp only [Finset.sum_empty, Real.log_zero]
    positivity
  · have habs : ∀ d, |primePowerLadder p β d| = primePowerLadder p β d :=
      fun d => abs_of_nonneg (primePowerLadder_nonneg p β d)
    simp only [habs]
    rw [sum_Icc_primePowerLadder hp hβ hN]
    have hlogle : ((Nat.log p N : ℕ) : ℝ) ≤ Real.log N / Real.log p := by
      rw [le_div_iff₀ hlogp]
      have hpow : p ^ (Nat.log p N) ≤ N := Nat.pow_log_le_self p (by omega)
      have h1 : Real.log (((p ^ (Nat.log p N) : ℕ)) : ℝ) ≤ Real.log N := by
        refine Real.log_le_log ?_ (by exact_mod_cast hpow)
        have : (0 : ℕ) < p ^ (Nat.log p N) := Nat.one_le_pow _ _ hp.pos
        exact_mod_cast this
      rw [show (((p ^ (Nat.log p N) : ℕ)) : ℝ) = (p : ℝ) ^ (Nat.log p N) from by push_cast; ring,
        Real.log_pow] at h1
      exact h1
    have hlognn : (0 : ℝ) ≤ ((Nat.log p N : ℕ) : ℝ) := Nat.cast_nonneg _
    have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
    have hstep : ((Nat.log p N : ℕ) : ℝ) ≤ (1 / Real.log p) * (1 + Real.log N) := by
      refine le_trans hlogle ?_
      rw [one_div, inv_mul_eq_div, div_le_div_iff_of_pos_right hlogp]
      linarith
    calc ((Nat.log p N : ℕ) : ℝ) ^ β ≤ ((1 / Real.log p) * (1 + Real.log N)) ^ β := by gcongr
      _ = (1 / Real.log p) ^ β * (1 + Real.log N) ^ β := by rw [mul_pow]

theorem exists_logPolyMass_multiLadder {β : ℕ → ℕ} (hβ : ∀ q, 1 ≤ β q) {ps : List ℕ}
    (hprime : ∀ q ∈ ps, q.Prime) :
    ∃ (C : ℝ) (m : ℕ), LogPolyMass (multiLadder β ps) C m := by
  induction ps with
  | nil =>
    refine ⟨1, 0, le_of_lt one_pos, fun N => ?_⟩
    have hbound : (∑ d ∈ Finset.Icc 1 N, |multiLadder β [] d|) ≤ 1 := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) by decide]
        simp
      · rw [Finset.sum_eq_single 1]
        · simp
        · intro d _ hd
          rw [multiLadder_nil, if_neg hd]
          simp
        · intro h
          exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩) h
    simpa using hbound
  | cons p ps ih =>
    have hpprime : p.Prime := hprime p (List.mem_cons_self ..)
    have hpsprime : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem _ hq)
    obtain ⟨C, m, hC⟩ := ih hpsprime
    exact ⟨C * (1 / Real.log p) ^ (β p), m + β p,
      by rw [multiLadder_cons]; exact hC.dconv (logPolyMass_primePowerLadder hpprime (hβ p))⟩

theorem tendsto_one_add_log_pow_div_atTop (m : ℕ) :
    Tendsto (fun x : ℝ => (1 + Real.log x) ^ m / x) atTop (nhds 0) := by
  have hrep : ∀ x : ℝ, (1 + Real.log x) ^ m / x
      = ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((Real.log x) ^ k / x) := by
    intro x
    rw [add_comm (1 : ℝ) (Real.log x), add_pow]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one]
    ring
  rw [show (fun x : ℝ => (1 + Real.log x) ^ m / x)
      = fun x : ℝ => ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((Real.log x) ^ k / x)
    from funext hrep]
  have h : Tendsto (fun x : ℝ =>
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((Real.log x) ^ k / x)) atTop
      (nhds (∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * 0)) :=
    tendsto_finsetSum _ fun k _ => (tendsto_log_pow_div_atTop k).const_mul _
  simpa using h

theorem tendsto_multiLadder_mass_div {β : ℕ → ℕ} (hβ : ∀ q, 1 ≤ β q) {ps : List ℕ}
    (hprime : ∀ q ∈ ps, q.Prime) :
    Tendsto (fun N : ℕ => (∑ d ∈ Finset.Icc 1 N, |multiLadder β ps d|) / N) atTop (nhds 0) := by
  obtain ⟨C, m, hC0, hC⟩ := exists_logPolyMass_multiLadder hβ hprime
  have hmaj : Tendsto (fun N : ℕ => C * ((1 + Real.log N) ^ m / N)) atTop (nhds 0) := by
    have h := (tendsto_one_add_log_pow_div_atTop m).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul C
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (0 : ℕ) < N := hN
      exact_mod_cast this
    have : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 N, |multiLadder β ps d| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (0 : ℕ) < N := hN
      exact_mod_cast this
    rw [div_le_iff₀ hNpos]
    have hkey := hC N
    have : C * ((1 + Real.log N) ^ m / N) * N = C * (1 + Real.log N) ^ m := by
      field_simp
    rw [this]
    exact hkey

/-! ### The lane coefficients, and the γ-affine structure theorem -/

theorem coeffDensity_multiLadder_nil (β : ℕ → ℕ) : coeffDensity (multiLadder β []) = 1 := by
  rw [coeffDensity]
  rw [tsum_eq_single 1 (fun d hd => by rw [multiLadder_nil, if_neg hd, zero_div])]
  simp

theorem coeffLogMass_multiLadder_nil (β : ℕ → ℕ) : coeffLogMass (multiLadder β []) = 0 := by
  rw [coeffLogMass]
  rw [tsum_eq_single 1 (fun d hd => by rw [multiLadder_nil, if_neg hd, zero_div, zero_mul])]
  simp

/-- **The two lanes are rational, respectively rational in the prime logarithms.** -/
theorem exists_rat_multiLadder_lanes {β : ℕ → ℕ} (hβ : ∀ q, 1 ≤ β q) {ps : List ℕ}
    (hprime : ∀ q ∈ ps, q.Prime) (hnodup : ps.Nodup) :
    ∃ (D : ℚ) (c : ℕ → ℚ),
      coeffDensity (multiLadder β ps) = (D : ℝ)
      ∧ coeffLogMass (multiLadder β ps) = ∑ q ∈ ps.toFinset, (c q : ℝ) * Real.log q := by
  induction ps with
  | nil =>
    refine ⟨1, fun _ => 0, ?_, ?_⟩
    · rw [coeffDensity_multiLadder_nil]; norm_num
    · rw [coeffLogMass_multiLadder_nil]
      simp
  | cons p ps ih =>
    have hpprime : p.Prime := hprime p (List.mem_cons_self ..)
    have hpsprime : ∀ q ∈ ps, q.Prime := fun q hq => hprime q (List.mem_cons_of_mem _ hq)
    have hpns : p ∉ ps := by
      rw [List.nodup_cons] at hnodup
      exact hnodup.1
    have hpsnodup : ps.Nodup := by
      rw [List.nodup_cons] at hnodup
      exact hnodup.2
    obtain ⟨D, c, hD, hc⟩ := ih hpsprime hpsnodup
    obtain ⟨dp, lp, hdp, hlp⟩ := exists_rat_stieltjesSinglePrime hpprime (hβ p)
    have hcop := coprimeSupport_multiLadder β hpsprime hpprime hpns
    have hsumA := summable_logWeight_multiLadder β hpsprime
    have hsumB := summable_logWeight_primePowerLadder hpprime (β p)
    have hBdens : coeffDensity (primePowerLadder p (β p)) = (dp : ℝ) := by
      rw [coeffDensity_primePowerLadder hpprime, hdp]
    have hBlog : coeffLogMass (primePowerLadder p (β p)) = Real.log p * (lp : ℝ) := by
      rw [coeffLogMass_primePowerLadder hpprime, hlp]
    refine ⟨D * dp, Function.update (fun q => c q * dp) p (D * lp), ?_, ?_⟩
    · rw [multiLadder_cons,
        coeffDensity_dconv (multiLadder_zero β ps) (primePowerLadder_zero p (β p))
          hcop hsumA hsumB, hD, hBdens]
      push_cast
      ring
    · rw [multiLadder_cons,
        coeffLogMass_dconv (multiLadder_zero β ps) (primePowerLadder_zero p (β p))
          hcop hsumA hsumB, hc, hD, hBdens, hBlog]
      have hpnf : p ∉ ps.toFinset := by
        rw [List.mem_toFinset]
        exact hpns
      rw [List.toFinset_cons, Finset.sum_insert hpnf]
      rw [Function.update_self]
      have hrest : ∀ q ∈ ps.toFinset,
          ((Function.update (fun q => c q * dp) p (D * lp) q : ℚ) : ℝ) * Real.log q
            = ((c q : ℝ) * Real.log q) * (dp : ℝ) := by
        intro q hq
        have hqne : q ≠ p := by
          intro h
          apply hpnf
          rw [← h]
          exact hq
        rw [Function.update_of_ne hqne]
        push_cast
        ring
      rw [Finset.sum_congr rfl hrest, ← Finset.sum_mul]
      push_cast
      ring

/-- **γ-affine structure of the generalized Stieltjes structure constants, in full generality.**
For every finite list of distinct primes and every multi-index of orders `≥ 1`, the regularized
limit exists and is a `ℚ`-linear combination of `γ` and the prime logarithms. -/
theorem tendsto_stieltjesMultiPrimeCutoff_rat {β : ℕ → ℕ} (hβ : ∀ q, 1 ≤ β q) {ps : List ℕ}
    (hprime : ∀ q ∈ ps, q.Prime) (hnodup : ps.Nodup) :
    ∃ (D : ℚ) (c : ℕ → ℚ),
      Tendsto (fun N : ℕ =>
          (∑ k ∈ Finset.Icc 1 N,
            (ps.map (fun q => ((padicValNat q k : ℕ) : ℝ) ^ β q)).prod / k)
            - (D : ℝ) * Real.log N)
        atTop (nhds ((D : ℝ) * Real.eulerMascheroniConstant
          - ∑ q ∈ ps.toFinset, (c q : ℝ) * Real.log q)) := by
  obtain ⟨D, c, hD, hc⟩ := exists_rat_multiLadder_lanes hβ hprime hnodup
  refine ⟨D, c, ?_⟩
  have hdev := tendsto_regularizedDivisorHarmonic
    (a := multiLadder β ps) (summable_logWeight_multiLadder β hprime)
    (tendsto_multiLadder_mass_div hβ hprime)
  rw [hD, hc] at hdev
  refine hdev.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [sum_divisors_multiLadder hβ hprime hnodup (by omega : k ≠ 0)]

end

end StieltjesGammaAffine
end RHTower
