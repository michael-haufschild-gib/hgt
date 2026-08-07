import GaloisForLFunctions.RHTower.RouteEStaticAntiscaleFrameDichotomy

/-!
# Static absolutely summable cross-prime kernel recurrence

Simultaneous recurrence of a finite prime head to antiscale phase `-1`, combined with absolute
control of the complete pair-indexed tail, annihilates every fixed absolutely summable
cross-prime kernel along arbitrarily large frequencies.  No positivity, Hermitian symmetry,
finite-rank, or diagonal hypothesis is used.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

open GaloisForLFunctions

/-- Antiscale seam attached to one prime character. -/
def routeEAntiscaleSeam (p : Nat.Primes) (t : ℝ) : ℂ :=
  1 + charFn t ((p : Nat.Primes) : ℕ)

/-- One ordered entry of a static cross-prime antiscale kernel. -/
def routeEStaticAbsoluteKernelTerm
    (K : Nat.Primes × Nat.Primes → ℂ) (q : Nat.Primes × Nat.Primes) (t : ℝ) : ℂ :=
  K q * routeEAntiscaleSeam q.1 t *
    (starRingEnd ℂ) (routeEAntiscaleSeam q.2 t)

theorem norm_routeEAntiscaleSeam_le_two (p : Nat.Primes) (t : ℝ) :
    ‖routeEAntiscaleSeam p t‖ ≤ 2 := by
  rw [routeEAntiscaleSeam]
  calc
    ‖(1 : ℂ) + charFn t ((p : Nat.Primes) : ℕ)‖
        ≤ ‖(1 : ℂ)‖ + ‖charFn t ((p : Nat.Primes) : ℕ)‖ := norm_add_le _ _
    _ = 2 := by norm_num

/-- Absolute ceiling for one cross-prime kernel entry. -/
theorem norm_routeEStaticAbsoluteKernelTerm_le_four
    (K : Nat.Primes × Nat.Primes → ℂ) (q : Nat.Primes × Nat.Primes) (t : ℝ) :
    ‖routeEStaticAbsoluteKernelTerm K q t‖ ≤ 4 * ‖K q‖ := by
  rw [routeEStaticAbsoluteKernelTerm, norm_mul, norm_mul, RCLike.norm_conj]
  have h₁ := norm_routeEAntiscaleSeam_le_two q.1 t
  have h₂ := norm_routeEAntiscaleSeam_le_two q.2 t
  have hprod : ‖routeEAntiscaleSeam q.1 t‖ * ‖routeEAntiscaleSeam q.2 t‖ ≤ 4 := by
    nlinarith [norm_nonneg (routeEAntiscaleSeam q.1 t),
      norm_nonneg (routeEAntiscaleSeam q.2 t)]
  nlinarith [norm_nonneg (K q)]

/-- An entrywise absolutely summable kernel defines the complete cross-prime form at every
frequency. -/
theorem summable_routeEStaticAbsoluteKernelTerm
    {K : Nat.Primes × Nat.Primes → ℂ}
    (hK : Summable (fun q : Nat.Primes × Nat.Primes => ‖K q‖)) (t : ℝ) :
    Summable (fun q : Nat.Primes × Nat.Primes =>
      routeEStaticAbsoluteKernelTerm K q t) := by
  exact Summable.of_norm_bounded (hK.mul_left 4)
    (fun q => norm_routeEStaticAbsoluteKernelTerm_le_four K q t)

/-- **Cofinal recurrence for every fixed absolutely summable cross-prime kernel.**  The complete
ordered-pair form has arbitrarily small modulus at arbitrarily large frequencies. -/
theorem exists_gt_norm_tsum_routeEStaticAbsoluteKernelTerm_lt
    {K : Nat.Primes × Nat.Primes → ℂ}
    (hK : Summable (fun q : Nat.Primes × Nat.Primes => ‖K q‖))
    {delta : ℝ} (hdelta : 0 < delta) (T : ℝ) :
    ∃ t : ℝ, T < t ∧
      ‖∑' q : Nat.Primes × Nat.Primes,
        routeEStaticAbsoluteKernelTerm K q t‖ < delta := by
  classical
  have hK4 : Summable (fun q : Nat.Primes × Nat.Primes => 4 * ‖K q‖) :=
    hK.mul_left 4
  have hhalf : (0 : ℝ) < delta / 2 := by linarith
  have htail : Filter.Tendsto (fun s : Finset (Nat.Primes × Nat.Primes) =>
      ∑' q : {r : Nat.Primes × Nat.Primes // r ∉ s}, 4 * ‖K (q : _)‖)
      Filter.atTop (nhds 0) :=
    tendsto_tsum_compl_atTop_zero
      (fun q : Nat.Primes × Nat.Primes => 4 * ‖K q‖)
  obtain ⟨A, hAtail⟩ := (htail.eventually_lt_const hhalf).exists
  set P : Finset Nat.Primes := A.image Prod.fst ∪ A.image Prod.snd with hP
  set H : ℝ := ∑ q ∈ A, ‖K q‖ with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun q _ => norm_nonneg (K q)
  have hdenom : (0 : ℝ) < H + 1 := by linarith
  set epsilon : ℝ := Real.sqrt ((delta / 2) / (H + 1)) with hepsilon
  have hquot : (0 : ℝ) < (delta / 2) / (H + 1) := div_pos hhalf hdenom
  have hepsilon_pos : 0 < epsilon := Real.sqrt_pos.mpr hquot
  have hepsilon_sq : epsilon ^ 2 = (delta / 2) / (H + 1) :=
    Real.sq_sqrt hquot.le
  have hind : LinearIndependent ℚ
      (fun p : {q : Nat.Primes // q ∈ P} => Real.log (((p : Nat.Primes) : ℕ) : ℝ)) :=
    linearIndependent_log_primes.comp
      (fun p : {q : Nat.Primes // q ∈ P} => (p : Nat.Primes)) Subtype.val_injective
  obtain ⟨t, ht, hclose⟩ :=
    kronecker_approx_atTop hind (fun _ => Real.pi) hepsilon_pos T
  refine ⟨t, ht, ?_⟩
  have hseam : ∀ p ∈ P, ‖routeEAntiscaleSeam p t‖ < epsilon := by
    intro p hp
    have hpclose := hclose ⟨p, hp⟩
    rw [Complex.exp_pi_mul_I] at hpclose
    have hchar : charFn t ((p : Nat.Primes) : ℕ) =
        expChar (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) t := by
      rw [charFn, expChar]
      congr 2
      push_cast
      ring
    rw [routeEAntiscaleSeam,
      show (1 : ℂ) + charFn t ((p : Nat.Primes) : ℕ) =
        charFn t ((p : Nat.Primes) : ℕ) - (-1) by ring,
      hchar]
    exact hpclose
  have hsummable := summable_routeEStaticAbsoluteKernelTerm hK t
  have hsplit := hsummable.sum_add_tsum_compl (s := A)
  have hheadbound :
      ‖∑ q ∈ A, routeEStaticAbsoluteKernelTerm K q t‖ < delta / 2 := by
    have hterm : ∀ q ∈ A,
        ‖routeEStaticAbsoluteKernelTerm K q t‖ ≤ ‖K q‖ * epsilon ^ 2 := by
      intro q hq
      have hq₁ : q.1 ∈ P := by
        rw [hP]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      have hq₂ : q.2 ∈ P := by
        rw [hP]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      have hs₁ := (hseam q.1 hq₁).le
      have hs₂ := (hseam q.2 hq₂).le
      rw [routeEStaticAbsoluteKernelTerm, norm_mul, norm_mul, RCLike.norm_conj]
      have hseamprod :
          ‖routeEAntiscaleSeam q.1 t‖ * ‖routeEAntiscaleSeam q.2 t‖ ≤
            epsilon * epsilon :=
        mul_le_mul hs₁ hs₂ (norm_nonneg _) hepsilon_pos.le
      calc
        ‖K q‖ * ‖routeEAntiscaleSeam q.1 t‖ * ‖routeEAntiscaleSeam q.2 t‖
            = ‖K q‖ *
                (‖routeEAntiscaleSeam q.1 t‖ * ‖routeEAntiscaleSeam q.2 t‖) := by ring
        _ ≤ ‖K q‖ * (epsilon * epsilon) :=
          mul_le_mul_of_nonneg_left hseamprod (norm_nonneg _)
        _ = ‖K q‖ * epsilon ^ 2 := by ring
    calc
      ‖∑ q ∈ A, routeEStaticAbsoluteKernelTerm K q t‖
          ≤ ∑ q ∈ A, ‖routeEStaticAbsoluteKernelTerm K q t‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ A, ‖K q‖ * epsilon ^ 2 := Finset.sum_le_sum hterm
      _ = (∑ q ∈ A, ‖K q‖) * epsilon ^ 2 := by rw [Finset.sum_mul]
      _ = H * epsilon ^ 2 := by rw [hH]
      _ < delta / 2 := by
        rw [hepsilon_sq]
        have hrewrite :
            H * ((delta / 2) / (H + 1)) =
              (H * (delta / 2)) / (H + 1) := by ring
        rw [hrewrite, div_lt_iff₀ hdenom]
        nlinarith
  have htailbound :
      ‖∑' q : {r : Nat.Primes × Nat.Primes // r ∉ A},
        routeEStaticAbsoluteKernelTerm K (q : _) t‖ < delta / 2 := by
    calc
      ‖∑' q : {r : Nat.Primes × Nat.Primes // r ∉ A},
          routeEStaticAbsoluteKernelTerm K (q : _) t‖
          ≤ ∑' q : {r : Nat.Primes × Nat.Primes // r ∉ A},
              ‖routeEStaticAbsoluteKernelTerm K (q : _) t‖ :=
            norm_tsum_le_tsum_norm (hsummable.norm.subtype _)
      _ ≤ ∑' q : {r : Nat.Primes × Nat.Primes // r ∉ A},
              4 * ‖K (q : _)‖ := by
            refine Summable.tsum_le_tsum (fun q => ?_)
              (hsummable.norm.subtype _) (hK4.subtype _)
            exact norm_routeEStaticAbsoluteKernelTerm_le_four K (q : _) t
      _ < delta / 2 := hAtail
  rw [← hsplit]
  calc
    ‖(∑ x ∈ A, routeEStaticAbsoluteKernelTerm K x t) +
        ∑' x : ((↑A : Set (Nat.Primes × Nat.Primes))ᶜ : Set _),
          routeEStaticAbsoluteKernelTerm K (x : _) t‖
        ≤ ‖∑ x ∈ A, routeEStaticAbsoluteKernelTerm K x t‖ +
            ‖∑' x : ((↑A : Set (Nat.Primes × Nat.Primes))ᶜ : Set _),
              routeEStaticAbsoluteKernelTerm K (x : _) t‖ := norm_add_le _ _
    _ < delta / 2 + delta / 2 := add_lt_add hheadbound htailbound
    _ = delta := by ring

/-- No fixed entrywise absolutely summable cross-prime kernel has a positive frequency-uniform
lower bound in modulus. -/
theorem not_exists_uniformly_coercive_routeEStaticAbsoluteKernel :
    ¬ ∃ K : Nat.Primes × Nat.Primes → ℂ,
      Summable (fun q : Nat.Primes × Nat.Primes => ‖K q‖) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
        c ≤ ‖∑' q : Nat.Primes × Nat.Primes,
          routeEStaticAbsoluteKernelTerm K q t‖ := by
  rintro ⟨K, hK, c, hc, hcoercive⟩
  obtain ⟨t, _ht, hsmall⟩ :=
    exists_gt_norm_tsum_routeEStaticAbsoluteKernelTerm_lt hK hc 0
  exact (not_lt_of_ge (hcoercive t)) hsmall

end

end RHTower.Sieve
