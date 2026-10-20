import GaloisForLFunctions.BezoutValuationIncidence.LogFreeLargeSieveFromWindowSandwich
import GaloisForLFunctions.RHTower.MultiplicativeLargeSieve

/-!
# The log-free large sieve for trigonometric polynomials and for primitive characters

The primal large sieve over the response frequencies holds on the initial window `n < N` as well
(multiply by one frequency to move the window to `[1, N]`). Indexing the frequencies by the Farey
set of order `Q` gives the textbook form

`Σ_{q ≤ Q} Σ_{(a,q) = 1} |Σ_{n<N} c_n e(n a/q)|² ≤ (N + 2Q² - 1) Σ |c_n|²`,

and the Gauss-sum reduction of primitive characters to additive frequencies gives the
multiplicative large sieve

`Σ_{q ≤ R} (q/φ(q)) Σ_{ψ primitive mod q} |Σ_{n<N} c_n ψ̄(n)|² ≤ (N + 2R² - 1) Σ |c_n|²`,

replacing `N + R²(1 + log(R²/2 + 1))`.
-/

open Finset RHTower.Sieve
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The initial window -/

theorem norm_sum_range_mul_pow_eq {ζ : ℂ} (hζ : ‖ζ‖ = 1) (N : ℕ) (y : ℕ → ℂ) :
    ‖∑ n ∈ range N, y n * ζ ^ n‖ = ‖∑ k ∈ Icc (0 + 1) (0 + N), y (k - 1) * ζ ^ k‖ := by
  have h : ∑ k ∈ Icc (0 + 1) (0 + N), y (k - 1) * ζ ^ k = ζ * ∑ n ∈ range N, y n * ζ ^ n := by
    rw [show Icc (0 + 1) (0 + N) = Ico (0 + 1) (N + 1) by ext; simp only [mem_Icc, mem_Ico]; omega,
      ← sum_Ico_add' (fun k => y (k - 1) * ζ ^ k) 0 N 1, range_eq_Ico, mul_sum]
    exact sum_congr rfl fun n _ => by rw [Nat.add_sub_cancel, pow_succ]; ring
  rw [h, norm_mul, hζ, one_mul]

/-- **Log-free large sieve on the initial window.** -/
theorem largeSieve_responseRoots_range {Q : ℕ} (hQ : 2 ≤ Q) {T : Finset ℂ}
    (hT : T ⊆ responseRoots Q) (N : ℕ) (y : ℕ → ℂ) :
    ∑ ζ ∈ T, ‖∑ n ∈ range N, y n * ζ ^ n‖ ^ 2 ≤
      ((N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) * ∑ n ∈ range N, ‖y n‖ ^ 2 := by
  have h := largeSieve_responseRoots hQ hT 0 N (fun k => y (k - 1))
  rw [show Icc (0 + 1) (0 + N) = Ico (0 + 1) (N + 1) by ext; simp only [mem_Icc, mem_Ico]; omega,
    ← sum_Ico_add' (fun k => ‖y (k - 1)‖ ^ 2) 0 N 1] at h
  simp only [Nat.add_sub_cancel, ← range_eq_Ico] at h
  refine le_of_eq_of_le (sum_congr rfl fun ζ hζ => ?_) h
  rw [norm_sum_range_mul_pow_eq (norm_eq_one_of_mem_responseRoots (hT hζ))]
  congr 2
  rw [show Icc (0 + 1) (0 + N) = Ico (0 + 1) (N + 1) by ext; simp only [mem_Icc, mem_Ico]; omega]

/-! ## §2. Farey points -/

theorem expSum_eq_sum_range (N : ℕ) (c : Fin N → ℂ) (θ : ℝ) :
    RHTower.Sieve.expSum N c θ =
      ∑ n ∈ range N, (if h : n < N then c ⟨n, h⟩ else 0) * circleFreq θ ^ n := by
  rw [RHTower.Sieve.expSum, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun n _ => ?_
  rw [dif_pos n.isLt]

/-- **Log-free large sieve on the Farey set.** -/
theorem largeSieve_expSum_fareySet_logFree (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (c : Fin N → ℂ) :
    ∑ p ∈ fareySet Q, ‖RHTower.Sieve.expSum N c ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 2 ≤
      ((N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) * ∑ n : Fin N, ‖c n‖ ^ 2 := by
  classical
  set f : ℕ × ℕ → ℂ := fun p => circleFreq ((p.1 : ℝ) / (p.2 : ℝ)) with hf
  set y : ℕ → ℂ := fun n => if h : n < N then c ⟨n, h⟩ else 0 with hy
  have hmem : ∀ p ∈ fareySet Q, f p ∈ responseRoots Q := by
    intro p hp
    obtain ⟨⟨_, _⟩, ⟨hq1, hqQ⟩, _, _⟩ := mem_fareySet.mp hp
    refine mem_biUnion.mpr ⟨p.2, mem_Icc.mpr ⟨hq1, hqQ⟩, ?_⟩
    rw [Polynomial.mem_nthRootsFinset (by omega) 1, hf, circleFreq_pow]
    have hq0 : (p.2 : ℝ) ≠ 0 := by exact_mod_cast (show p.2 ≠ 0 by omega)
    rw [mul_div_cancel₀ _ hq0, circleFreq_natCast]
  have hinj : ∀ p ∈ fareySet Q, ∀ r ∈ fareySet Q, f p = f r → p = r := by
    intro p hp r hr hpr
    by_contra hne
    have hsep := fareySet_sep p hp r hr hne
    have hchord := four_mul_toIntDist_le_norm_sub ((p.1 : ℝ) / (p.2 : ℝ)) ((r.1 : ℝ) / (r.2 : ℝ))
    have hfp : ‖f p‖ = 1 := norm_circleFreq _
    simp only [hf] at hpr hfp
    rw [← hpr, conj_mul_self_of_norm_eq_one hfp, sub_self, norm_zero] at hchord
    have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
    have : (0 : ℝ) < 1 / (Q : ℝ) ^ (2 : ℕ) := by positivity
    linarith
  have hls := largeSieve_responseRoots_range hQ (T := (fareySet Q).image f)
    (fun ζ hζ => by
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hζ
      exact hmem p hp) N y
  rw [sum_image hinj] at hls
  have hc : ∑ n ∈ range N, ‖y n‖ ^ 2 = ∑ n : Fin N, ‖c n‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => ‖y n‖ ^ 2)]
    exact sum_congr rfl fun n _ => by simp only [hy, dif_pos n.isLt]
  rw [hc] at hls
  refine le_of_eq_of_le (sum_congr rfl fun p _ => ?_) hls
  rw [expSum_eq_sum_range]

/-- **Log-free large sieve in textbook form.** -/
theorem largeSieve_expSum_double_logFree (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (c : Fin N → ℂ) :
    ∑ q ∈ Icc 1 Q, ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖RHTower.Sieve.expSum N c ((a : ℝ) / (q : ℝ))‖ ^ 2 ≤
      ((N : ℝ) + 2 * (Q : ℝ) ^ 2 - 1) * ∑ n : Fin N, ‖c n‖ ^ 2 := by
  classical
  have hdisj : (↑(Icc 1 Q) : Set ℕ).PairwiseDisjoint
      (fun q => ((Icc 1 q).filter (fun a => Nat.Coprime a q)).image (fun a => (a, q))) := by
    intro q _ q' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    rintro p hp hp'
    rw [mem_image] at hp hp'
    obtain ⟨a, _, rfl⟩ := hp
    obtain ⟨a', _, heq⟩ := hp'
    exact hne (congrArg Prod.snd heq).symm
  have hbase := largeSieve_expSum_fareySet_logFree N hQ c
  rw [fareySet_eq_biUnion, sum_biUnion hdisj] at hbase
  have hinner : ∀ q ∈ Icc 1 Q,
      ∑ p ∈ ((Icc 1 q).filter (fun a => Nat.Coprime a q)).image (fun a => (a, q)),
          ‖RHTower.Sieve.expSum N c ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 2 =
        ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
          ‖RHTower.Sieve.expSum N c ((a : ℝ) / (q : ℝ))‖ ^ 2 :=
    fun q _ => sum_image fun a _ a' _ heq => congrArg Prod.fst heq
  rwa [sum_congr rfl hinner] at hbase

/-! ## §3. Primitive characters -/

open Classical in
/-- **The log-free multiplicative large sieve.** For `R ≥ 2` and coefficients `c_n`, `n < N`,
`Σ_{q ≤ R} (q/φ(q)) Σ_{ψ primitive mod q} |Σ_{n<N} c_n ψ̄(n)|² ≤ (N + 2R² - 1) Σ |c_n|²`. -/
theorem multiplicative_largeSieve_logFree (N R : ℕ) (hR : 2 ≤ R) (c : ℕ → ℂ) :
    ∑ r ∈ range R, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖∑ n ∈ range N, c n * conj (ψ n)‖ ^ 2 ≤
      ((N : ℝ) + 2 * (R : ℝ) ^ 2 - 1) * ∑ n ∈ range N, ‖c n‖ ^ 2 := by
  classical
  set c' : Fin N → ℂ := fun n => c n with hc'
  have hterm : ∀ r ∈ range R, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖∑ n ∈ range N, c n * conj (ψ n)‖ ^ 2 ≤
      ∑ a ∈ (Icc 1 (r + 1)).filter (fun a => Nat.Coprime a (r + 1)),
          ‖RHTower.Sieve.expSum N c' ((a : ℝ) / ((r + 1 : ℕ) : ℝ))‖ ^ 2 := by
    intro r _
    have hφ : (0 : ℝ) < (r + 1).totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos r)
    have hq : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
    have h := RHTower.sum_primitive_normSq_le (r := r + 1) N c
    have h2 := mul_le_mul_of_nonneg_left h
      (by positivity : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) / (r + 1).totient)
    refine h2.trans (le_of_eq ?_)
    rw [← mul_assoc, show ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ((r + 1).totient / ((r + 1 : ℕ) : ℝ)) = 1 by field_simp, one_mul,
      RHTower.sum_units_eq_sum_coprime]
    refine sum_congr rfl fun a _ => ?_
    congr 2
    rw [RHTower.Sieve.expSum, Finset.sum_range]
    refine sum_congr rfl fun n _ => ?_
    rw [RHTower.stdChar_natCast_mul]
  refine (sum_le_sum hterm).trans ?_
  have hreindex : ∑ r ∈ range R, ∑ a ∈ (Icc 1 (r + 1)).filter (fun a => Nat.Coprime a (r + 1)),
        ‖RHTower.Sieve.expSum N c' ((a : ℝ) / ((r + 1 : ℕ) : ℝ))‖ ^ 2 =
      ∑ q ∈ Icc 1 R, ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖RHTower.Sieve.expSum N c' ((a : ℝ) / (q : ℝ))‖ ^ 2 := by
    rw [range_eq_Ico, sum_Ico_add' (f := fun q =>
      ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖RHTower.Sieve.expSum N c' ((a : ℝ) / (q : ℝ))‖ ^ 2) 0 R 1]
    have hI : Ico (0 + 1) (R + 1) = Icc 1 R := by
      ext x
      simp only [mem_Ico, mem_Icc]
      omega
    rw [hI]
  rw [hreindex]
  have hls := largeSieve_expSum_double_logFree N hR c'
  have hcoef : ∑ n : Fin N, ‖c' n‖ ^ 2 = ∑ n ∈ range N, ‖c n‖ ^ 2 := by
    rw [Finset.sum_range]
  rwa [hcoef] at hls

end

end GaloisForLFunctions.BezoutValuationIncidence
