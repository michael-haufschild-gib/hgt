import GaloisForLFunctions.RHTower.Sieve.LargeSmoothPart

/-!
# The sharp lower tail

Fibring over the `z`-smooth part costs one sieve error per fibre, and the number of fibres is what
previously forced `log z` to be of order `log X / log log X`, losing a power of `log log X` against
the expected `(log X)^{-I(t)}`.

Cutting the fibring at a level `M` removes that constraint.  Below the cut there are at most `M`
fibres, so the total sieve error is `M · (2/log Y + Y² (log z)^(4 : ℕ))` — affordable as soon as `M` and
`Y²` are small powers of the interval length.  Above the cut the integers are handled by the
divisor window of `LargeSmoothPart.lean`, whose cost is the window size times `(b-a)/M + 1`.

The density is now `2/log Y`, supplied by the Selberg sieve at a level `Y` that may be a fixed power
of the interval length; it no longer degrades with `z`.  The smooth weight still contributes
`(log z)^t / t^k`, so with `log Y ≍ log(b-a)` and `k = t · log log(b-a)` the exponent is exactly

`t - t log t - 1 = -I(t)`,

the card's own entropy rate, with a `(log log)^{-t}` gain rather than a loss.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **Fibring below a cut.**  The integers of `Ioc a b` with at most `k` distinct prime factors
split into those whose `z`-smooth part is at most `M` — distributed among at most `M` rough-number
counts — and those whose smooth part exceeds `M`. -/
theorem card_omega_le_le_sum_restricted (a b z k M : ℕ) :
    (#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k})
      ≤ ∑ s ∈ {s ∈ smoothUpTo (Nat.primesLE z) M | s.primeFactors.card ≤ k},
          (#{m ∈ Finset.Ioc (a / s) (b / s) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m})
        + (#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k ∧ M < smoothPart z n}) := by
  classical
  set A : Finset ℕ := {n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} with hA
  set A₁ : Finset ℕ :=
    {n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k ∧ smoothPart z n ≤ M} with hA₁
  set A₂ : Finset ℕ :=
    {n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k ∧ M < smoothPart z n} with hA₂
  set T : Finset ℕ := {s ∈ smoothUpTo (Nat.primesLE z) M | s.primeFactors.card ≤ k} with hT
  have hsplit : A.card = A₁.card + A₂.card := by
    have h := Finset.card_filter_add_card_filter_not (s := A) (p := fun n => smoothPart z n ≤ M)
    have he₁ : {n ∈ A | smoothPart z n ≤ M} = A₁ := by
      rw [hA, hA₁, Finset.filter_filter]
    have he₂ : {n ∈ A | ¬ smoothPart z n ≤ M} = A₂ := by
      rw [hA, hA₂, Finset.filter_filter]
      refine Finset.filter_congr ?_
      intro n _
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, not_le.1 h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, not_le.2 h2⟩
    rw [he₁, he₂] at h
    omega
  have hfib : ∀ n ∈ A₁, smoothPart z n ∈ T := by
    intro n hn
    obtain ⟨hmem, hcard, hcut⟩ := Finset.mem_filter.1 hn
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.1 hmem
    have hn0 : n ≠ 0 := by omega
    have hspos : 0 < smoothPart z n := smoothPart_pos z n
    have hsub : (smoothPart z n).primeFactors ⊆ Nat.primesLE z := by
      rw [primeFactors_smoothPart hn0 z]
      intro p hp
      obtain ⟨hpn, hpz⟩ := Finset.mem_filter.1 hp
      exact Nat.mem_primesLE.2 ⟨hpz, Nat.prime_of_mem_primeFactors hpn⟩
    have hscard : (smoothPart z n).primeFactors.card ≤ k := by
      have hsplit' := card_primeFactors_roughPart_add hn0 z
      omega
    exact Finset.mem_filter.2 ⟨mem_smoothUpTo.2 ⟨⟨hspos, hcut⟩, hsub⟩, hscard⟩
  have hbound : A₁.card
      ≤ ∑ s ∈ T, (#{m ∈ Finset.Ioc (a / s) (b / s) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m}) := by
    rw [Finset.card_eq_sum_card_fiberwise hfib]
    refine Finset.sum_le_sum ?_
    intro σ hσ
    obtain ⟨hσmem, -⟩ := Finset.mem_filter.1 hσ
    obtain ⟨⟨hσ1, hσM⟩, -⟩ := mem_smoothUpTo.1 hσmem
    have hσpos : 0 < σ := hσ1
    refine Finset.card_le_card_of_injOn (fun n => n / σ) ?_ ?_
    · intro n hn
      obtain ⟨hnA, hns⟩ := Finset.mem_filter.1 hn
      obtain ⟨hmem, -, -⟩ := Finset.mem_filter.1 hnA
      obtain ⟨han, hnb⟩ := Finset.mem_Ioc.1 hmem
      have hn0 : n ≠ 0 := by omega
      have hmul : smoothPart z n * roughPart z n = n := smoothPart_mul_roughPart hn0 z
      have hσdvd : σ ∣ n := hns ▸ smoothPart_dvd z n
      have hn_eq : n = σ * roughPart z n := by
        conv_lhs => rw [← hmul]
        rw [hns]
      have hdiv : n / σ = roughPart z n := by
        conv_lhs => rw [hn_eq]
        exact Nat.mul_div_cancel_left _ hσpos
      have hupper : n / σ ≤ b / σ := Nat.div_le_div_right hnb
      have hlower : a / σ < n / σ := by
        rw [Nat.div_lt_iff_lt_mul hσpos, Nat.div_mul_cancel hσdvd]
        exact han
      refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hlower, hupper⟩, ?_⟩
      intro p hp
      show ¬ p ∣ n / σ
      rw [hdiv]
      exact not_dvd_roughPart hn0 hp
    · intro x hx y hy hxy
      obtain ⟨hxA, hxs⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
      obtain ⟨hyA, hys⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
      obtain ⟨hxmem, -, -⟩ := Finset.mem_filter.1 hxA
      obtain ⟨hymem, -, -⟩ := Finset.mem_filter.1 hyA
      have hxdvd : σ ∣ x := hxs ▸ smoothPart_dvd z x
      have hydvd : σ ∣ y := hys ▸ smoothPart_dvd z y
      have hxe : σ * (x / σ) = x := Nat.mul_div_cancel' hxdvd
      have hye : σ * (y / σ) = y := Nat.mul_div_cancel' hydvd
      have hq : x / σ = y / σ := hxy
      rw [← hxe, ← hye, hq]
  omega

/-- The index set below the cut has at most `M` members. -/
theorem card_smoothUpTo_le (z M k : ℕ) :
    (#{s ∈ smoothUpTo (Nat.primesLE z) M | s.primeFactors.card ≤ k}) ≤ M := by
  classical
  have hsub : {s ∈ smoothUpTo (Nat.primesLE z) M | s.primeFactors.card ≤ k} ⊆ Finset.Icc 1 M := by
    intro s hs
    obtain ⟨hmem, -⟩ := Finset.mem_filter.1 hs
    obtain ⟨⟨h1, h2⟩, -⟩ := mem_smoothUpTo.1 hmem
    exact Finset.mem_Icc.2 ⟨h1, h2⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Nat.card_Icc]
  omega

/-- **Sharp lower tail.**  Three explicit terms: the Selberg main term with density `2/log Y`
weighted by the tilted smooth sum, the sieve error of at most `M` fibres, and the divisor-window
cost of the integers with a large smooth part.  The density no longer depends on `z`, so `log Y`
may be taken of the order of `log (b-a)`. -/
theorem card_omega_le_le_sharp (a b z Y k M : ℕ) (hab : a ≤ b) (hY : 1 ≤ Y) (hYz : Y ≤ z)
    (hz : 2 ≤ z) (hM : 1 ≤ M) (hlog : 0 < Real.log Y) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ)
      ≤ ((b : ℝ) - a) * (2 / Real.log Y) * smoothTiltBound z k t
        + (M : ℝ) * (2 / Real.log Y + selbergFibreError z Y)
        + (((b : ℝ) - a) / M + 1)
            * ∑ j ∈ Finset.range (k + 1),
                (((Nat.primesLE z).card * Nat.log 2 (M * z)).choose j : ℝ) := by
  classical
  set T : Finset ℕ := {s ∈ smoothUpTo (Nat.primesLE z) M | s.primeFactors.card ≤ k} with hT
  set R : ℝ := 2 / Real.log Y with hR
  set E : ℝ := selbergFibreError z Y with hE
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hE0 : 0 ≤ E := selbergFibreError_nonneg hz Y
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hstart : ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ)
      ≤ (∑ σ ∈ T, ((#{m ∈ Finset.Ioc (a / σ) (b / σ) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m}) : ℝ))
        + ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k ∧ M < smoothPart z n} : ℕ) : ℝ) := by
    have := card_omega_le_le_sum_restricted a b z k M
    exact_mod_cast this
  have hfibre : ∀ σ ∈ T,
      ((#{m ∈ Finset.Ioc (a / σ) (b / σ) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m}) : ℝ)
        ≤ ((b : ℝ) - a) * R * (1 / σ) + (R + E) := by
    intro σ hσ
    obtain ⟨hσmem, -⟩ := Finset.mem_filter.1 hσ
    obtain ⟨⟨hσ1, hσM⟩, -⟩ := mem_smoothUpTo.1 hσmem
    have hσpos : 0 < σ := hσ1
    have hσR : (0 : ℝ) < σ := by exact_mod_cast hσpos
    have hdivle : a / σ ≤ b / σ := Nat.div_le_div_right hab
    have hsieve := card_rough_Ioc_le_selberg (a / σ) (b / σ) z Y hdivle hY hYz hz hlog
    have hgap : ((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ) ≤ ((b : ℝ) - a) / σ + 1 := by
      have hb := (cast_div_bounds (d := σ) (n := b) hσpos).1
      have ha := (cast_div_bounds (d := σ) (n := a) hσpos).2
      have hsp : ((b : ℝ) - a) / σ = (b : ℝ) / σ - (a : ℝ) / σ := by ring
      rw [hsp]
      linarith
    have hmul : (((b / σ : ℕ) : ℝ) - ((a / σ : ℕ) : ℝ)) * R ≤ (((b : ℝ) - a) / σ + 1) * R :=
      mul_le_mul_of_nonneg_right hgap hR0
    have hfin : (((b : ℝ) - a) / σ + 1) * R = ((b : ℝ) - a) * R * (1 / σ) + R := by
      field_simp
    linarith
  have hsum : ∑ σ ∈ T, (1 : ℝ) / σ ≤ smoothTiltBound z k t := by
    rw [hT]
    exact sum_smoothUpTo_card_le_inv_le_exp ht0 ht1 k hz M
  have hcard : (T.card : ℝ) ≤ (M : ℝ) := by
    have := card_smoothUpTo_le z M k
    rw [hT]
    exact_mod_cast this
  have hmain : (∑ σ ∈ T, ((#{m ∈ Finset.Ioc (a / σ) (b / σ) | ∀ p ∈ Nat.primesLE z, ¬ p ∣ m}) : ℝ))
      ≤ ((b : ℝ) - a) * R * smoothTiltBound z k t + (M : ℝ) * (R + E) := by
    refine le_trans (Finset.sum_le_sum hfibre) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hpos1 : 0 ≤ ((b : ℝ) - a) * R := mul_nonneg hlen hR0
    have h1 : ((b : ℝ) - a) * R * ∑ σ ∈ T, (1 : ℝ) / σ
        ≤ ((b : ℝ) - a) * R * smoothTiltBound z k t :=
      mul_le_mul_of_nonneg_left hsum hpos1
    have h2 : (T.card : ℝ) * (R + E) ≤ (M : ℝ) * (R + E) :=
      mul_le_mul_of_nonneg_right hcard (by linarith)
    linarith
  have hlarge := card_large_smoothPart_le a b z k M hM hab
  linarith

end RHTower.Sieve
