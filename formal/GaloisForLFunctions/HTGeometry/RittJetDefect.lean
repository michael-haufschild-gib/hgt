import GaloisForLFunctions.HTGeometry.RittLinearizerJets
import GaloisForLFunctions.HTGeometry.RittBaseExponent
import GaloisForLFunctions.HTGeometry.RittSecondJetAffineConnection
import GaloisForLFunctions.HTGeometry.RittPrefixFieldStability

/-!
# The shift defect of a jet, and where it vanishes

The shift of the `n`-th jet of a linearizer is `(q/ρ^n)` times itself plus a *defect* lying in the
span of the lower jets.  Differentiating the relation one level at a time gives the recursion

`defect_{n+1} = (dK(q/ρ^n)/ρ)·d^[n]τ + ρ^{-1}·d(defect_n)`,   `defect_1 = 0`,

so the coefficient of the top available jet obeys `λ_{n+1} = (dK(q/ρ^n) + λ_n)/ρ`.  With
`dK(q/ρ^n) = −n·q·(dρ)/ρ^{n+1}` this has the closed form

`λ_n = −C(n,2)·q·(dρ)/ρ^{n+1}`,

whose binomial coefficient is nonzero exactly from `n = 2` on.  So above jet order one the defect is
a nonzero base multiple of `d^[n−1]τ` modulo the span of the still lower jets, and `d^[n−1]τ` is not
in the field those generate: the defect vanishes only at jet orders `0` and `1`, where the shift acts
on the jet by pure scaling.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace RittFrame

variable (Fr : RittFrame K L)

/-- The defect by which the shift of the `n`-th jet misses being a pure scaling. -/
def jetDefect (τ : L) (q : K) (n : ℕ) : L :=
  Fr.σ (Fr.d^[n] τ) - algebraMap K L (q / Fr.ρ ^ n) * Fr.d^[n] τ

variable {Fr}

theorem d_algebraMap_mul (a : K) (x : L) :
    Fr.d (algebraMap K L a * x) = algebraMap K L (Fr.dK a) * x + algebraMap K L a * Fr.d x := by
  rw [Fr.d_mul, Fr.d_base]

/-- The derivative of the level multiplier. -/
theorem dK_level_multiplier {q : K} (hqconst : Fr.dK q = 0) (k : ℕ) :
    Fr.dK (q / Fr.ρ ^ k) = -((k : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (k + 1)) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hpow : Fr.dK (Fr.ρ ^ k) = (k : K) * Fr.ρ ^ k * Fr.dK Fr.ρ / Fr.ρ := by
    cases k with
    | zero => simp [Fr.dK_one]
    | succ j =>
        rw [Fr.dK_pow_succ]
        field_simp
        push_cast
        ring
  rw [Fr.dK_div (pow_ne_zero k hρ0), hqconst, hpow]
  field_simp
  ring

/-- The defect vanishes at jet order one. -/
theorem jetDefect_one {τ : L} {q : K} (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) : Fr.jetDefect τ q 1 = 0 := by
  have h := Fr.sigma_d_eq_of_shift hqconst hshift
  show Fr.σ (Fr.d τ) - algebraMap K L (q / Fr.ρ ^ (1 : ℕ)) * Fr.d τ = 0
  rw [pow_one, h, sub_self]

/-- **The defect recursion.** -/
theorem jetDefect_succ {τ : L} {q : K} (n : ℕ) :
    Fr.jetDefect τ q (n + 1)
      = algebraMap K L (Fr.dK (q / Fr.ρ ^ n) / Fr.ρ) * Fr.d^[n] τ
        + algebraMap K L (Fr.ρ)⁻¹ * Fr.d (Fr.jetDefect τ q n) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hρL : algebraMap K L Fr.ρ ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hρ0
  have hexp : Fr.σ (Fr.d^[n] τ)
      = algebraMap K L (q / Fr.ρ ^ n) * Fr.d^[n] τ + Fr.jetDefect τ q n := by
    rw [jetDefect]; ring
  have hderiv := congrArg Fr.d hexp
  rw [Fr.chain, Fr.d_add, d_algebraMap_mul] at hderiv
  rw [← Function.iterate_succ_apply' Fr.d] at hderiv
  simp only [Nat.succ_eq_add_one] at hderiv
  have e1 : algebraMap K L Fr.ρ * algebraMap K L (q / Fr.ρ ^ (n + 1))
      = algebraMap K L (q / Fr.ρ ^ n) := by
    rw [← map_mul]
    congr 1
    rw [pow_succ]
    field_simp
  have e2 : algebraMap K L Fr.ρ * algebraMap K L (Fr.dK (q / Fr.ρ ^ n) / Fr.ρ)
      = algebraMap K L (Fr.dK (q / Fr.ρ ^ n)) := by
    rw [← map_mul]
    congr 1
    field_simp
  have e3 : algebraMap K L Fr.ρ * algebraMap K L (Fr.ρ)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hρ0, map_one]
  have hgoal : algebraMap K L Fr.ρ
      * (Fr.σ (Fr.d^[n + 1] τ) - algebraMap K L (q / Fr.ρ ^ (n + 1)) * Fr.d^[n + 1] τ)
      = algebraMap K L Fr.ρ * (algebraMap K L (Fr.dK (q / Fr.ρ ^ n) / Fr.ρ) * Fr.d^[n] τ
        + algebraMap K L (Fr.ρ)⁻¹ * Fr.d (Fr.jetDefect τ q n)) := by
    linear_combination hderiv - (Fr.d^[n] τ) * e2 - (Fr.d^[n + 1] τ) * e1
      - (Fr.d (Fr.jetDefect τ q n)) * e3
  exact mul_left_cancel₀ hρL hgoal

end RittFrame

variable [CharZero K]

omit [CharZero K] in
/-- **The leading coefficient of the defect.**  Above jet order one the defect is a base multiple of
the top available jet, with binomial coefficient, modulo the span of the lower jets. -/
theorem jetDefect_leading (Fr : RittFrame K L) {τ : L} {q : K} (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) :
    ∀ m : ℕ, Fr.jetDefect τ q (m + 2)
      - algebraMap K L (-(((m + 2).choose 2 : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (m + 3)))
        * Fr.d^[m + 1] τ ∈ Fr.jetSpan τ m := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  intro m
  induction m with
  | zero =>
      have h : Fr.jetDefect τ q (0 + 2)
          = algebraMap K L (Fr.dK (q / Fr.ρ ^ (1 : ℕ)) / Fr.ρ) * Fr.d^[1] τ
            + algebraMap K L (Fr.ρ)⁻¹ * Fr.d (Fr.jetDefect τ q 1) :=
        RittFrame.jetDefect_succ 1
      rw [RittFrame.jetDefect_one hqconst hshift, Fr.d_zero, mul_zero, add_zero,
        RittFrame.dK_level_multiplier hqconst 1] at h
      have hcoef : -((((1 : ℕ) : K)) * q * Fr.dK Fr.ρ / Fr.ρ ^ (1 + 1)) / Fr.ρ
          = -(((((0 + 2).choose 2 : ℕ)) : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (0 + 3)) := by
        have h2 : ((0 + 2).choose 2) = 1 := by decide
        rw [h2]
        push_cast
        field_simp
      rw [Fr.jetSpan_zero, Submodule.mem_bot, h, hcoef, sub_self]
  | succ m ih =>
      set lam : K := -(((m + 2).choose 2 : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (m + 3)) with hlam
      set r : L := Fr.jetDefect τ q (m + 2) - algebraMap K L lam * Fr.d^[m + 1] τ with hr
      have hrmem : r ∈ Fr.jetSpan τ m := ih
      have hdec : Fr.jetDefect τ q (m + 2) = algebraMap K L lam * Fr.d^[m + 1] τ + r := by
        rw [hr]; ring
      have h : Fr.jetDefect τ q (m + 1 + 2)
          = algebraMap K L (Fr.dK (q / Fr.ρ ^ (m + 2)) / Fr.ρ) * Fr.d^[m + 2] τ
            + algebraMap K L (Fr.ρ)⁻¹ * Fr.d (Fr.jetDefect τ q (m + 2)) :=
        RittFrame.jetDefect_succ (m + 2)
      rw [hdec, Fr.d_add, RittFrame.d_algebraMap_mul,
        ← Function.iterate_succ_apply' Fr.d] at h
      have hnewL : algebraMap K L (Fr.dK (q / Fr.ρ ^ (m + 2)) / Fr.ρ)
          + algebraMap K L (Fr.ρ)⁻¹ * algebraMap K L lam
          = algebraMap K L
            (-((((m + 1) + 2).choose 2 : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ ((m + 1) + 3))) := by
        rw [← map_mul, ← map_add]
        congr 1
        rw [RittFrame.dK_level_multiplier hqconst (m + 2), hlam]
        have hch : (((m + 1) + 2).choose 2 : K)
            = ((m + 2 : ℕ) : K) + ((m + 2).choose 2 : K) := by
          have hnat : ((m + 1) + 2).choose 2 = (m + 2) + (m + 2).choose 2 := by
            have hp := Nat.choose_succ_succ (m + 2) 1
            simpa [Nat.choose_one_right] using hp
          rw [hnat]
          push_cast
          ring
        rw [hch]
        field_simp
        ring
      have hmem1 : algebraMap K L (Fr.dK lam) * Fr.d^[m + 1] τ ∈ Fr.jetSpan τ (m + 1) := by
        rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Fr.mem_jetSpan (Nat.lt_succ_self m))
      have hmem2 : Fr.d r ∈ Fr.jetSpan τ (m + 1) := Fr.d_mem_jetSpan_succ hrmem
      have hmem3 : algebraMap K L (Fr.ρ)⁻¹
          * (algebraMap K L (Fr.dK lam) * Fr.d^[m + 1] τ + Fr.d r) ∈ Fr.jetSpan τ (m + 1) := by
        rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ hmem1 hmem2)
      have hgoal : Fr.jetDefect τ q (m + 1 + 2)
          - algebraMap K L
              (-((((m + 1) + 2).choose 2 : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ ((m + 1) + 3)))
            * Fr.d^[m + 1 + 1] τ
          = algebraMap K L (Fr.ρ)⁻¹
            * (algebraMap K L (Fr.dK lam) * Fr.d^[m + 1] τ + Fr.d r) := by
        rw [h]
        linear_combination (Fr.d^[m + 2] τ) * hnewL
      rw [hgoal]
      exact hmem3

/-- **The shift defect is nonzero above jet order one.**  So a jet whose shift is a pure scaling has
order zero or one. -/
theorem jetDefect_ne_zero (Fr : RittFrame K L) {τ : L} {q : K} (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0) (hdρ : Fr.dK Fr.ρ ≠ 0) (m : ℕ)
    (hjet : Fr.d^[m + 1] τ ∉ Fr.jetPrefixField τ (m + 1)) :
    Fr.jetDefect τ q (m + 2) ≠ 0 := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  intro hzero
  set lam : K := -(((m + 2).choose 2 : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (m + 3)) with hlam
  have hch0 : (((m + 2).choose 2 : ℕ) : K) ≠ 0 := by
    have hpos : 0 < (m + 2).choose 2 := Nat.choose_pos (by omega)
    exact Nat.cast_ne_zero.mpr (by omega)
  have hlam0 : lam ≠ 0 := by
    rw [hlam, neg_ne_zero]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hch0 hq) hdρ) (pow_ne_zero _ hρ0)
  have hmem : Fr.jetDefect τ q (m + 2) - algebraMap K L lam * Fr.d^[m + 1] τ ∈ Fr.jetSpan τ m :=
    jetDefect_leading Fr hqconst hshift m
  rw [hzero, zero_sub] at hmem
  have hmem' : algebraMap K L lam * Fr.d^[m + 1] τ ∈ Fr.jetSpan τ m := by
    simpa using neg_mem hmem
  have hsub : algebraMap K L lam * Fr.d^[m + 1] τ ∈ Fr.jetPrefixField τ (m + 1) :=
    Fr.jetSpan_le_intermediateField (fun j hj => Fr.jet_mem_jetPrefixField (by omega)) _ hmem'
  have hlamL : algebraMap K L lam ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hlam0
  refine hjet ?_
  have hinv : algebraMap K L lam⁻¹ ∈ Fr.jetPrefixField τ (m + 1) :=
    IntermediateField.algebraMap_mem _ _
  have := mul_mem hinv hsub
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hlam0, map_one, one_mul] at this

end GaloisForLFunctions.HTGeometry
