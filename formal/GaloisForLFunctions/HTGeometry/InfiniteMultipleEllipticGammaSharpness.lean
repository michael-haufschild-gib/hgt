import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGamma
import GaloisForLFunctions.HTGeometry.PrimaryFactorLogExpansion

/-!
# Sharpness of the genus threshold for infinite-order multiple elliptic gamma products

The singleton occupations form a subfamily of the whole occupation spectrum, and along them the
canonical product reduces to one primary factor per nome.  A summable majorant on any disc of
positive radius therefore forces `(g+1)`-summability of the nomes themselves.

Combined with the already proved sufficiency, normal convergence of the infinite-order genus-`g`
product on some disc is *equivalent* to `(g+1)`-summability of the nome family.  The genus spectrum
is thus exactly the set of admissible Hadamard schemes, not merely a sufficient supply of them.
-/

namespace HTGeometry

open scoped BigOperators

theorem norm_nomeMonomial_le_one {ι : Type*} (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (ν : ι →₀ ℕ) : ‖nomeMonomial p ν‖ ≤ 1 := by
  classical
  rw [nomeMonomial, Finsupp.prod, norm_prod]
  refine Finset.prod_le_one (fun a _ => by positivity) (fun a _ => ?_)
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (le_of_lt (hp_lt a))

theorem nomeMonomial_single {ι : Type*} [DecidableEq ι] (p : ι → ℂ) (a : ι) :
    nomeMonomial p (Finsupp.single a 1) = p a := by
  rw [nomeMonomial, Finsupp.prod_single_index (by simp)]
  simp

/-- **Necessity of the genus.**  A summable majorant for the centred occupation factors, uniform on
a disc of positive radius, forces the nome family to be `(g+1)`-summable. -/
theorem summable_nome_pow_of_normal_majorant {ι : Type*} (g : ℕ) (p : ι → ℂ)
    {R : ℝ} (hR : 0 < R) (M : (ι →₀ ℕ) → ℝ)
    (hM : ∀ ν : ι →₀ ℕ, ∀ x : ℂ, ‖x‖ ≤ R →
      ‖primaryFactor g (x * nomeMonomial p ν) - 1‖ ≤ M ν)
    (hMsum : Summable M) :
    Summable (fun a => ‖p a‖ ^ (g + 1)) := by
  classical
  refine summable_pow_of_normal_majorant g p hR (fun a => M (Finsupp.single a 1)) ?_ ?_
  · intro a x hx
    have h := hM (Finsupp.single a 1) x hx
    rwa [nomeMonomial_single p a] at h
  · exact hMsum.comp_injective (Finsupp.single_left_injective one_ne_zero)

/-- **The exact convergence criterion.**  For a nonvanishing nome family inside the unit disc,
`(g+1)`-summability of the nomes is equivalent to the existence of a summable majorant for the
centred occupation factors on some disc of positive radius — that is, to normal convergence of the
genus-`g` canonical product. -/
theorem summable_nome_pow_iff_exists_normal_majorant {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) :
    Summable (fun a => ‖p a‖ ^ (g + 1)) ↔
      ∃ R : ℝ, 0 < R ∧ ∃ M : (ι →₀ ℕ) → ℝ, Summable M ∧
        ∀ ν : ι →₀ ℕ, ∀ x : ℂ, ‖x‖ ≤ R →
          ‖primaryFactor g (x * nomeMonomial p ν) - 1‖ ≤ M ν := by
  classical
  constructor
  · intro hsum
    have hq_ne : ∀ ν : ι →₀ ℕ, nomeMonomial p ν ≠ 0 := nomeMonomial_ne_zero p hp_ne
    have hq_sum : Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ (g + 1)) :=
      (summable_nomeMonomial_pow_iff g p hp_lt).2 hsum
    refine ⟨1, one_pos, fun ν => Real.exp g * ‖nomeMonomial p ν‖ ^ (g + 1), ?_, ?_⟩
    · exact hq_sum.mul_left _
    · intro ν x hx
      have h1 : ‖nomeMonomial p ν‖ ≤ 1 := norm_nomeMonomial_le_one p hp_lt ν
      have hz : ‖x * nomeMonomial p ν‖ ≤ 1 := by
        rw [norm_mul]
        nlinarith [norm_nonneg x, norm_nonneg (nomeMonomial p ν), hx, h1]
      have hbound := primaryFactor_sub_one_norm_le g hz
      calc ‖primaryFactor g (x * nomeMonomial p ν) - 1‖
          ≤ Real.exp g * ‖x * nomeMonomial p ν‖ ^ (g + 1) := hbound
        _ ≤ Real.exp g * ‖nomeMonomial p ν‖ ^ (g + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
            rw [norm_mul, mul_pow]
            have hx1 : ‖x‖ ^ (g + 1) ≤ 1 := by
              have := pow_le_one₀ (norm_nonneg x) hx (n := g + 1)
              simpa using this
            nlinarith [pow_nonneg (norm_nonneg (nomeMonomial p ν)) (g + 1),
              pow_nonneg (norm_nonneg x) (g + 1)]
  · rintro ⟨R, hR, M, hMsum, hM⟩
    exact summable_nome_pow_of_normal_majorant g p hR M hM hMsum

end HTGeometry
