import GaloisForLFunctions.RHTower.Sieve.DirichletPowerConvolution
import GaloisForLFunctions.RHTower.Sieve.PrimeCubeSupport

/-!
# Powers of a prime-supported Dirichlet polynomial

When the coefficients are supported on the primes, every point of a `k`-fold convolution fibre is a
tuple of primes with a fixed product, so each of its entries is one of the at most `k` prime factors
of that product.  The fibre therefore has at most `k^k` points — a bound independent of the length
of the polynomial.  This is what makes the `2k`-th moment of a prime-supported Dirichlet polynomial
usable with a free exponent.
-/

namespace RHTower.Sieve

open Finset

/-- The part of a `k`-fold convolution fibre whose entries all lie in a support. -/
private noncomputable def powFibreOn (k N : ℕ) (S : Finset (Fin N)) (j : Fin (N ^ k)) :
    Finset (Fin k → Fin N) :=
  (powFibre k N j).filter (fun p => ∀ i, p i ∈ S)

/-- **The `ℓ²` norm of the `k`-fold convolution, through a support.** -/
private theorem sum_normSq_convPow_le_of_support (k N : ℕ) (a : Fin N → ℂ) (S : Finset (Fin N))
    (hsupp : ∀ n : Fin N, a n ≠ 0 → n ∈ S) {D : ℝ}
    (hD : ∀ j : Fin (N ^ k), ((powFibreOn k N S j).card : ℝ) ≤ D) (hD0 : 0 ≤ D) :
    ∑ j : Fin (N ^ k), ‖dirichletPowerConvolutionConvPow k N a j‖ ^ (2 : ℕ)
      ≤ D * (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ k := by
  classical
  set g : (Fin k → Fin N) → ℝ := fun p => ‖∏ i, a (p i)‖ with hg
  have hconv : ∀ j : Fin (N ^ k),
      dirichletPowerConvolutionConvPow k N a j = ∑ p ∈ powFibreOn k N S j, ∏ i, a (p i) := by
    intro j
    rw [dirichletPowerConvolutionConvPow, powFibreOn]
    refine (Finset.sum_filter_of_ne (fun p _ hne => ?_)).symm
    intro i
    refine hsupp _ (fun hzero => hne ?_)
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
  have hfibre : ∀ j : Fin (N ^ k),
      ‖dirichletPowerConvolutionConvPow k N a j‖ ^ (2 : ℕ) ≤ D * ∑ p ∈ powFibreOn k N S j, g p ^ (2 : ℕ) := by
    intro j
    have hnorm : ‖dirichletPowerConvolutionConvPow k N a j‖ ≤ ∑ p ∈ powFibreOn k N S j, g p := by
      rw [hconv j]
      exact norm_sum_le _ _
    have hsq : ‖dirichletPowerConvolutionConvPow k N a j‖ ^ (2 : ℕ) ≤ (∑ p ∈ powFibreOn k N S j, g p) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hcs : (∑ p ∈ powFibreOn k N S j, g p) ^ (2 : ℕ)
        ≤ ((powFibreOn k N S j).card : ℝ) * ∑ p ∈ powFibreOn k N S j, g p ^ (2 : ℕ) :=
      sq_sum_le_card_mul_sum_sq
    have hsum0 : (0 : ℝ) ≤ ∑ p ∈ powFibreOn k N S j, g p ^ (2 : ℕ) :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    have hmul : ((powFibreOn k N S j).card : ℝ) * ∑ p ∈ powFibreOn k N S j, g p ^ (2 : ℕ)
        ≤ D * ∑ p ∈ powFibreOn k N S j, g p ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right (hD j) hsum0
    linarith
  have hsum : ∑ j : Fin (N ^ k), ‖dirichletPowerConvolutionConvPow k N a j‖ ^ (2 : ℕ)
      ≤ ∑ j : Fin (N ^ k), D * ∑ p ∈ powFibreOn k N S j, g p ^ (2 : ℕ) :=
    Finset.sum_le_sum fun j _ => hfibre j
  have hsubset : ∀ j : Fin (N ^ k), powFibreOn k N S j ⊆ powFibre k N j := by
    intro j
    exact Finset.filter_subset _ _
  have hstep : ∀ j : Fin (N ^ k),
      ∑ p ∈ powFibreOn k N S j, g p ^ (2 : ℕ) ≤ ∑ p ∈ powFibre k N j, g p ^ (2 : ℕ) := by
    intro j
    exact Finset.sum_le_sum_of_subset_of_nonneg (hsubset j) (fun p _ _ => sq_nonneg _)
  have hsum2 : ∑ j : Fin (N ^ k), D * ∑ p ∈ powFibreOn k N S j, g p ^ (2 : ℕ)
      ≤ ∑ j : Fin (N ^ k), D * ∑ p ∈ powFibre k N j, g p ^ (2 : ℕ) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hstep j) hD0
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin k → Fin N)))
    (t := (Finset.univ : Finset (Fin (N ^ k)))) (g := fun p => dirichletPowerConvolutionPowIdx p)
    (f := fun p : Fin k → Fin N => g p ^ (2 : ℕ))
    (fun p _ => Finset.mem_univ _)
  have hcollect : ∑ j : Fin (N ^ k), D * ∑ p ∈ powFibre k N j, g p ^ (2 : ℕ)
      = D * ∑ p : Fin k → Fin N, g p ^ (2 : ℕ) := by
    simp only [powFibre]
    rw [← Finset.mul_sum, ← hfib]
  have hprod : ∑ p : Fin k → Fin N, g p ^ (2 : ℕ) = (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ k := by
    have hterm : ∀ p : Fin k → Fin N, g p ^ (2 : ℕ) = ∏ i, ‖a (p i)‖ ^ (2 : ℕ) := by
      intro p
      rw [hg]
      simp only [norm_prod]
      rw [← Finset.prod_pow]
    have hconst : (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ k
        = ∏ _i : Fin k, (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [hterm]
    rw [hconst,
      Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin N)))
        (fun _ n => ‖a n‖ ^ (2 : ℕ)), Fintype.piFinset_univ]
  rw [hcollect, hprod] at hsum2
  linarith

/-- **A prime-supported `k`-fold fibre has at most `k^k` points.**  Every entry of a fibre point is
a prime factor of the anchored product, and that product has at most `k` prime factors. -/
theorem powFibreOn_primeSupport_card_le (k N : ℕ) (j : Fin (N ^ k)) :
    ((powFibreOn k N (primeSupport N) j).card : ℝ) ≤ (k : ℝ) ^ k := by
  classical
  rcases Finset.eq_empty_or_nonempty (powFibreOn k N (primeSupport N) j) with hempty | ⟨p₀, hp₀⟩
  · rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hmem : ∀ p ∈ powFibreOn k N (primeSupport N) j,
        (∏ i, ((p i : ℕ) + 1)) = (j : ℕ) + 1 ∧ ∀ i, Nat.Prime ((p i : ℕ) + 1) := by
      intro p hp
      rw [powFibreOn, Finset.mem_filter, powFibre, Finset.mem_filter] at hp
      obtain ⟨⟨-, hidx⟩, hS⟩ := hp
      refine ⟨?_, fun i => ?_⟩
      · rw [← dirichletPowerConvolutionPowIdx_val_add_one p, hidx]
      · have := hS i
        rw [primeSupport, Finset.mem_filter] at this
        exact this.2
    obtain ⟨hprod₀, hprime₀⟩ := hmem p₀ hp₀
    have hjpos : 0 < (j : ℕ) + 1 := Nat.succ_pos _
    -- every prime factor of the anchored product is one of the `k` entries of `p₀`
    have hsubset : ((j : ℕ) + 1).primeFactors
        ⊆ Finset.image (fun i : Fin k => ((p₀ i : ℕ) + 1)) Finset.univ := by
      intro q hq
      rw [Nat.mem_primeFactors] at hq
      obtain ⟨hqp, hqd, -⟩ := hq
      rw [← hprod₀] at hqd
      obtain ⟨i, -, hdvd⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 hqd
      refine Finset.mem_image.2 ⟨i, Finset.mem_univ i, ?_⟩
      exact ((Nat.prime_dvd_prime_iff_eq hqp (hprime₀ i)).1 hdvd).symm
    have hcardM : (((j : ℕ) + 1).primeFactors).card ≤ k := by
      refine le_trans (Finset.card_le_card hsubset) ?_
      refine le_trans (Finset.card_image_le) ?_
      simp
    -- the fibre injects into tuples of prime factors
    have hinj : (powFibreOn k N (primeSupport N) j).card
        ≤ (Fintype.piFinset (fun _ : Fin k => ((j : ℕ) + 1).primeFactors)).card := by
      refine Finset.card_le_card_of_injOn (fun p i => ((p i : ℕ) + 1)) ?_ ?_
      · intro p hp
        obtain ⟨hprod, hprime⟩ := hmem p hp
        refine Fintype.mem_piFinset.2 fun i => ?_
        refine Nat.mem_primeFactors.2 ⟨hprime i, ?_, by omega⟩
        rw [← hprod]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      · intro p _ q _ hpq
        funext i
        have hi : ((p i : ℕ) + 1) = ((q i : ℕ) + 1) := congrFun hpq i
        exact Fin.ext (by omega)
    have hcardpi : (Fintype.piFinset (fun _ : Fin k => ((j : ℕ) + 1).primeFactors)).card
        = (((j : ℕ) + 1).primeFactors).card ^ k := by
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hcardpi] at hinj
    have hcast : ((powFibreOn k N (primeSupport N) j).card : ℝ)
        ≤ ((((j : ℕ) + 1).primeFactors).card : ℝ) ^ k := by
      have := (Nat.cast_le (α := ℝ)).2 hinj
      rwa [Nat.cast_pow] at this
    refine le_trans hcast ?_
    refine pow_le_pow_left₀ (by positivity) ?_ k
    exact_mod_cast hcardM

/-- **The `ℓ²` norm of the `k`-th power of a prime-supported coefficient vector.** -/
theorem sum_normSq_convPow_le_of_prime_support (k N : ℕ) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1)) :
    ∑ j : Fin (N ^ k), ‖dirichletPowerConvolutionConvPow k N a j‖ ^ (2 : ℕ)
      ≤ (k : ℝ) ^ k * (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ k := by
  classical
  refine sum_normSq_convPow_le_of_support k N a (primeSupport N) (fun n hn => ?_)
    (fun j => powFibreOn_primeSupport_card_le k N j) (by positivity)
  rw [primeSupport, Finset.mem_filter]
  exact ⟨Finset.mem_univ n, hsupp n hn⟩

/-- **The `2k`-th moment of a prime-supported Dirichlet polynomial at separated frequencies.**  No
power of the length enters the coefficient factor: only `k^k`. -/
theorem powMoment_dirPoly_prime_support (k N : ℕ) (hk : 1 ≤ k) (hN : 2 ≤ N) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 → Nat.Prime ((n : ℕ) + 1))
    {lam : ℕ → ℝ} {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T) :
    ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ (2 * k)
      ≤ (T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ k : ℕ) : ℝ))
          * ((k : ℝ) ^ k * (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ k) := by
  classical
  have hNk : 2 ≤ N ^ k := le_trans hN (Nat.le_self_pow (by omega) N)
  have hmv := largeValues_dirPoly (N ^ k) hNk (dirichletPowerConvolutionConvPow k N a) hδ hT hgap hlow R hhigh
  have hrewrite : ∀ r : ℕ,
      ‖dirPoly (N ^ k) (dirichletPowerConvolutionConvPow k N a) (lam r)‖ ^ (2 : ℕ) = ‖dirPoly N a (lam r)‖ ^ (2 * k) := by
    intro r
    rw [dirichletPowerConvolutionDirPoly_convPow, norm_pow, ← pow_mul, mul_comm k 2]
  simp only [hrewrite] at hmv
  refine le_trans hmv ?_
  have hlogNk : (0 : ℝ) ≤ Real.log ((N ^ k : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ N ^ k := by omega
    exact_mod_cast this
  have hfactor : (0 : ℝ)
      ≤ (T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ k : ℕ) : ℝ)) := by
    have hcast : (0 : ℝ) ≤ ((N ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)) := by
      nlinarith
    have h2 : (0 : ℝ) ≤ 1 / δ + 2 * Real.log ((N ^ k : ℕ) : ℝ) := by
      have : (0 : ℝ) < 1 / δ := by positivity
      linarith
    exact mul_nonneg h1 h2
  exact mul_le_mul_of_nonneg_left (sum_normSq_convPow_le_of_prime_support k N a hsupp) hfactor

end RHTower.Sieve
