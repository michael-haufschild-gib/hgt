/-
# The ξ-zeros are square-summable: convergence exponent below two

The zeros of the completed Riemann `ξ`, counted with multiplicity, have summable inverse squares:
`∑_ρ mult(ρ) / ‖ρ‖² < ∞`.  In Hadamard/Weierstrass language this says the convergence exponent of the
`ξ`-zero sequence is `< 2`, the input a genus-one product over the zeros consumes.

The engine is the unconditional zero-density bound `xi_zeroCount_growth`: the total `ξ`-zero
multiplicity in the disc `B(2, r)` is `N(r) = O(r · log r)`.  Decompose the divisor support into dyadic
shells `S_k = {ρ : 2ᵏ ≤ ‖ρ − 2‖ < 2ᵏ⁺¹}`.  The multiplicity mass of `S_k` is `≤ N(2ᵏ⁺¹) = O(2ᵏ·k)`,
while every point of `S_k` contributes `≤ mult / (2ᵏ)² = mult · 4⁻ᵏ`; hence shell `k` contributes
`≤ 4⁻ᵏ · N(2ᵏ⁺¹) = O(k · 2⁻ᵏ)`, and `∑_k O(k·2⁻ᵏ) < ∞` (a geometric-times-polynomial series).  The
centre shift from `‖ρ − 2‖` to `‖ρ‖` costs only a bounded factor: for `‖ρ − 2‖ ≥ 4` one has
`‖ρ‖ ≥ ‖ρ − 2‖/2`, so `1/‖ρ‖² ≤ 4/‖ρ − 2‖²`, and the finitely many zeros with `‖ρ − 2‖ < 4` form a
fixed finite mass.  Summability is obtained by bounding every finite partial sum of the (nonnegative)
series by the fixed constant `(core mass) + 4·∑_k 4⁻ᵏ·N(2ᵏ⁺¹)`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.XiZeroDensity

open Complex Metric Function Filter MeromorphicOn

namespace RHTower

/-- The dyadic shell index of a point `ρ`, i.e. the `k` with `2ᵏ ≤ ‖ρ − 2‖ < 2ᵏ⁺¹` when `‖ρ − 2‖ ≥ 1`.
Defined as `⌊log₂ ⌊‖ρ − 2‖⌋⌋`. -/
noncomputable def xiShell (ρ : ℂ) : ℕ := Nat.log 2 ⌊‖ρ - 2‖⌋₊

/-- Lower dyadic bound: if `‖ρ − 2‖ ≥ 4` then `2^{xiShell ρ} ≤ ‖ρ − 2‖`. -/
lemma two_pow_xiShell_le {ρ : ℂ} (h : (4:ℝ) ≤ ‖ρ - 2‖) : (2:ℝ) ^ xiShell ρ ≤ ‖ρ - 2‖ := by
  have h1 : (1:ℝ) ≤ ‖ρ - 2‖ := by linarith
  have hm1 : 1 ≤ ⌊‖ρ - 2‖⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  calc (2:ℝ) ^ xiShell ρ
      = ((2 ^ Nat.log 2 ⌊‖ρ - 2‖⌋₊ : ℕ) : ℝ) := by rw [xiShell]; push_cast; ring
    _ ≤ (⌊‖ρ - 2‖⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    _ ≤ ‖ρ - 2‖ := Nat.floor_le (by positivity)

/-- Upper dyadic bound: `‖ρ − 2‖ < 2^{xiShell ρ + 1}` for every `ρ`. -/
lemma norm_lt_two_pow_xiShell_succ (ρ : ℂ) : ‖ρ - 2‖ < (2:ℝ) ^ (xiShell ρ + 1) := by
  have h1 : ‖ρ - 2‖ < (⌊‖ρ - 2‖⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnat : ⌊‖ρ - 2‖⌋₊ + 1 ≤ 2 ^ (xiShell ρ + 1) := by
    rw [xiShell]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : (⌊‖ρ - 2‖⌋₊ : ℝ) + 1 ≤ (2:ℝ) ^ (xiShell ρ + 1) := by
    calc (⌊‖ρ - 2‖⌋₊ : ℝ) + 1 = ((⌊‖ρ - 2‖⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ (xiShell ρ + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (2:ℝ) ^ (xiShell ρ + 1) := by push_cast; ring
  linarith

/-- The divisor of `ξ` on any set is nonnegative pointwise (`ξ` is entire). -/
lemma xi_divisor_nonneg (U : Set ℂ) (z : ℂ) : 0 ≤ MeromorphicOn.divisor xi U z := by
  have h := (xi_analyticOnNhd U).divisor_nonneg
  have := (Function.locallyFinsuppWithin.le_def.mp h) z
  simpa using this

/-- The pure real inequality behind the shell estimate: with `a = ‖ρ‖`, `b = ‖ρ − 2‖`, multiplicity
`d ≥ 0`, and `2ˢ ≤ b`, `4 ≤ b`, `b/2 ≤ a`, one has `d/a² ≤ 4·d·4⁻ˢ`. -/
lemma shell_term_bound {a b d : ℝ} {s : ℕ} (hd : 0 ≤ d) (hb4 : 4 ≤ b)
    (hab : b / 2 ≤ a) (hbs : (2:ℝ) ^ s ≤ b) : d / a ^ 2 ≤ 4 * d * (1/4) ^ s := by
  have hbpos : 0 < b := by linarith
  have hapos : 0 < a := by linarith
  have h1 : d / a ^ 2 ≤ d / (b/2) ^ 2 :=
    div_le_div_of_nonneg_left hd (by positivity) (pow_le_pow_left₀ (by positivity) hab 2)
  have h2 : d / (b/2) ^ 2 = 4 * d / b ^ 2 := by field_simp; ring
  have h3 : 4 * d / b ^ 2 ≤ 4 * d / ((2:ℝ) ^ s) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ (by positivity) hbs 2)
  have h4 : 4 * d / ((2:ℝ) ^ s) ^ 2 = 4 * d * (1/4) ^ s := by
    have he : ((2:ℝ) ^ s) ^ 2 = (4:ℝ) ^ s := by rw [← pow_mul, mul_comm s 2, pow_mul]; norm_num
    rw [he, show (1/4:ℝ) = (4:ℝ)⁻¹ from by norm_num, inv_pow, div_eq_mul_inv]
  calc d / a ^ 2 ≤ d / (b/2) ^ 2 := h1
    _ = 4 * d / b ^ 2 := h2
    _ ≤ 4 * d / ((2:ℝ) ^ s) ^ 2 := h3
    _ = 4 * d * (1/4) ^ s := h4

/-- **The ξ-zeros are square-summable.**  Indexed by the actual divisor-support subtype and weighted by
the integer multiplicity `divisor ξ` at each zero, the series `∑_ρ mult(ρ)/‖ρ‖²` converges.  Equivalently,
the convergence exponent of the completed-zeta zero sequence is strictly below `2`. -/
theorem xi_zero_multiplicity_inv_sq_summable :
    Summable (fun ρ : ↥(MeromorphicOn.divisor xi Set.univ).support =>
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
  classical
  obtain ⟨C, hCpos, hN⟩ := xi_zeroCount_growth
  set D := MeromorphicOn.divisor xi Set.univ with hDdef
  set f : ↥D.support → ℝ := fun ρ => ((D (ρ : ℂ) : ℝ)) / ‖(ρ : ℂ)‖ ^ 2 with hfdef
  have hfnn : ∀ ρ : ↥D.support, 0 ≤ f ρ := by
    intro ρ
    apply div_nonneg _ (by positivity)
    exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
  -- The dominating dyadic series and its convergence.
  set bnd : ℕ → ℝ :=
    fun k => (1/4:ℝ) ^ k * (C * (1 + (2:ℝ) ^ (k+1)) * Real.log (2 + (2:ℝ) ^ (k+1))) with hbnddef
  have hbndnn : ∀ k, 0 ≤ bnd k := by
    intro k
    have hlog0 : 0 ≤ Real.log (2 + (2:ℝ) ^ (k+1)) :=
      Real.log_nonneg (by nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) (k+1)])
    simp only [hbnddef]; positivity
  have hbndsum : Summable bnd := by
    have hs1 : Summable (fun n : ℕ => (n:ℝ) * (1/2) ^ n) := by
      have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1/2)
        (by rw [Real.norm_eq_abs]; norm_num)
      simpa using this
    have hs2 : Summable (fun n : ℕ => (1/2:ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hdom : Summable (fun k : ℕ => (4 * C * Real.log 2) * (((k:ℝ) + 3) * (1/2) ^ k)) := by
      apply Summable.mul_left
      have := hs1.add (hs2.mul_left 3)
      refine this.congr (fun k => ?_); ring
    refine Summable.of_nonneg_of_le hbndnn (fun k => ?_) hdom
    simp only [hbnddef]
    have hp : (0:ℝ) < (2:ℝ) ^ (k+1) := by positivity
    have hx1 : (1:ℝ) ≤ (2:ℝ) ^ (k+1) := one_le_pow₀ (by norm_num)
    have hlog : Real.log (2 + (2:ℝ) ^ (k+1)) ≤ ((k:ℝ) + 3) * Real.log 2 := by
      have hle : (2:ℝ) + (2:ℝ) ^ (k+1) ≤ (2:ℝ) ^ (k+3) := by
        have h23 : (2:ℝ) ^ (k+3) = 4 * (2:ℝ) ^ (k+1) := by ring
        rw [h23]; nlinarith [hx1]
      calc Real.log (2 + (2:ℝ) ^ (k+1)) ≤ Real.log ((2:ℝ) ^ (k+3)) :=
            Real.log_le_log (by positivity) hle
        _ = ((k:ℝ) + 3) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    have hlin : (1:ℝ) + (2:ℝ) ^ (k+1) ≤ 4 * (2:ℝ) ^ k := by
      have h2k : (2:ℝ) ^ (k+1) = 2 * (2:ℝ) ^ k := by ring
      have h1k : (1:ℝ) ≤ (2:ℝ) ^ k := one_le_pow₀ (by norm_num)
      rw [h2k]; linarith
    have hkey : (1/4:ℝ) ^ k * (2:ℝ) ^ k = (1/2) ^ k := by rw [← mul_pow]; norm_num
    have hlog0 : 0 ≤ Real.log (2 + (2:ℝ) ^ (k+1)) := Real.log_nonneg (by nlinarith [hp])
    calc (1/4:ℝ) ^ k * (C * (1 + (2:ℝ) ^ (k+1)) * Real.log (2 + (2:ℝ) ^ (k+1)))
        ≤ (1/4:ℝ) ^ k * (C * (4 * (2:ℝ) ^ k) * (((k:ℝ) + 3) * Real.log 2)) := by gcongr
      _ = 4 * C * Real.log 2 * (((k:ℝ) + 3) * (1/2) ^ k) := by rw [← hkey]; ring
  set B : ℝ := ∑' k, bnd k with hBdef
  -- The bounded core: finitely many zeros with `‖ρ − 2‖ < 4`.
  have hLF : LocallyFiniteSupport D.toFun := Function.locallyFinsupp.locallyFiniteSupport D
  have hcore_fin : {ρ : ↥D.support | ‖(ρ : ℂ) - 2‖ < 4}.Finite := by
    apply Set.Finite.of_finite_image _ (Subtype.val_injective.injOn)
    apply Set.Finite.subset (hLF.finite_inter_support_of_isCompact (isCompact_closedBall (2:ℂ) 4))
    rintro z ⟨ρ, hρ, rfl⟩
    exact ⟨by rw [mem_closedBall, dist_eq_norm]; exact le_of_lt hρ, ρ.2⟩
  set coreFin := hcore_fin.toFinset with hcoreFin
  set P : ↥D.support → Prop := fun ρ => ‖(ρ : ℂ) - 2‖ < 4 with hP
  -- Bound every finite partial sum by the fixed constant `(core mass) + 4·B`.
  refine summable_of_sum_le (c := (∑ ρ ∈ coreFin, f ρ) + 4 * B) hfnn (fun u => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not u P f]
  apply add_le_add
  · -- Core part: subset of the fixed finite core.
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ρ hρ
      rw [hcoreFin, Set.Finite.mem_toFinset]
      exact (Finset.mem_filter.mp hρ).2
    · intro ρ _ _; exact hfnn ρ
  · -- Far part: dyadic shells against the density bound.
    set uf := u.filter (fun ρ => ¬ P ρ) with hufdef
    have hfar4 : ∀ ρ ∈ uf, (4:ℝ) ≤ ‖(ρ : ℂ) - 2‖ := by
      intro ρ hρ
      have := (Finset.mem_filter.mp hρ).2
      simp only [hP, not_lt] at this; exact this
    -- Termwise shell domination `f ρ ≤ 4·mult(ρ)·4^{-shell}`.
    set G : ↥D.support → ℝ := fun ρ => 4 * (D (ρ : ℂ) : ℝ) * (1/4) ^ xiShell (ρ : ℂ) with hGdef
    have hfG : ∀ ρ ∈ uf, f ρ ≤ G ρ := by
      intro ρ hρ
      have hb4 : (4:ℝ) ≤ ‖(ρ : ℂ) - 2‖ := hfar4 ρ hρ
      have hd : (0:ℝ) ≤ (D (ρ : ℂ) : ℝ) := by exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
      have hab : ‖(ρ : ℂ) - 2‖ / 2 ≤ ‖(ρ : ℂ)‖ := by
        have htri : ‖(ρ : ℂ) - 2‖ ≤ ‖(ρ : ℂ)‖ + ‖(2:ℂ)‖ := norm_sub_le _ _
        have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
        rw [h2] at htri; linarith
      have hbs : (2:ℝ) ^ xiShell (ρ : ℂ) ≤ ‖(ρ : ℂ) - 2‖ := two_pow_xiShell_le hb4
      have key := shell_term_bound (a := ‖(ρ : ℂ)‖) (b := ‖(ρ : ℂ) - 2‖)
        (d := (D (ρ : ℂ) : ℝ)) (s := xiShell (ρ : ℂ)) hd hb4 hab hbs
      simp only [hfdef, hGdef]; exact key
    calc ∑ ρ ∈ uf, f ρ
        ≤ ∑ ρ ∈ uf, G ρ := Finset.sum_le_sum hfG
      _ = ∑ b ∈ uf.image (fun ρ : ↥D.support => xiShell (ρ : ℂ)),
            ∑ ρ ∈ uf.filter (fun ρ : ↥D.support => xiShell (ρ : ℂ) = b), G ρ :=
          (Finset.sum_fiberwise_of_maps_to
            (fun ρ hρ => Finset.mem_image_of_mem (fun ρ : ↥D.support => xiShell (ρ : ℂ)) hρ) G).symm
      _ ≤ ∑ b ∈ uf.image (fun ρ : ↥D.support => xiShell (ρ : ℂ)), 4 * bnd b := by
          apply Finset.sum_le_sum
          intro b _
          set fib := uf.filter (fun ρ : ↥D.support => xiShell (ρ : ℂ) = b) with hfibdef
          set r : ℝ := (2:ℝ) ^ (b+1) with hrdef
          have hr1 : (1:ℝ) ≤ r := by rw [hrdef]; exact one_le_pow₀ (by norm_num)
          have hmem : ∀ ρ ∈ fib, (ρ : ℂ) ∈ closedBall (2:ℂ) r := by
            intro ρ hρ
            have hb' : xiShell (ρ : ℂ) = b := (Finset.mem_filter.mp hρ).2
            rw [mem_closedBall, dist_eq_norm, hrdef, ← hb']
            exact le_of_lt (norm_lt_two_pow_xiShell_succ (ρ : ℂ))
          set Db := MeromorphicOn.divisor xi (closedBall (2:ℂ) r) with hDb
          have hrestrEq : D.restrict (Set.subset_univ (closedBall (2:ℂ) r)) = Db :=
            MeromorphicOn.divisor_restrict xi_analyticOnNhd_univ.meromorphicOn _
          have hrestr : ∀ z ∈ closedBall (2:ℂ) r, D z = Db z := by
            intro z hz
            rw [← hrestrEq, Function.locallyFinsuppWithin.restrict_apply, if_pos hz]
          have hDbfin : (Function.support ⇑Db).Finite := Db.finiteSupport (isCompact_closedBall _ _)
          have hZ : (∑ ρ ∈ fib, D (ρ : ℂ)) ≤ ∑ᶠ v, Db v := by
            calc (∑ ρ ∈ fib, D (ρ : ℂ))
                = ∑ ρ ∈ fib, Db (ρ : ℂ) :=
                  Finset.sum_congr rfl (fun ρ hρ => hrestr (ρ : ℂ) (hmem ρ hρ))
              _ = ∑ z ∈ fib.image (Subtype.val), Db z :=
                  (Finset.sum_image (fun a _ b _ h => Subtype.ext h)).symm
              _ ≤ ∑ z ∈ hDbfin.toFinset, Db z := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro z hz
                    rw [Finset.mem_image] at hz
                    obtain ⟨ρ, hρ, rfl⟩ := hz
                    rw [Set.Finite.mem_toFinset]
                    apply Function.mem_support.mpr
                    rw [← hrestr (ρ : ℂ) (hmem ρ hρ)]
                    exact Function.mem_support.mp ρ.2
                  · intro z _ _; exact xi_divisor_nonneg _ z
              _ = ∑ᶠ v, Db v :=
                  (finsum_eq_finsetSum_of_support_subset Db (by rw [hDbfin.coe_toFinset])).symm
          have hmass : ((∑ ρ ∈ fib, D (ρ : ℂ) : ℤ) : ℝ) ≤ C * (1 + r) * Real.log (2 + r) := by
            calc ((∑ ρ ∈ fib, D (ρ : ℂ) : ℤ) : ℝ)
                ≤ ((∑ᶠ v, Db v : ℤ) : ℝ) := by exact_mod_cast hZ
              _ ≤ C * (1 + r) * Real.log (2 + r) := hN r hr1
          have hshell_eq : ∀ ρ ∈ fib, G ρ = (4 * (1/4) ^ b) * (D (ρ : ℂ) : ℝ) := by
            intro ρ hρ
            have hb' : xiShell (ρ : ℂ) = b := (Finset.mem_filter.mp hρ).2
            simp only [hGdef]; rw [hb']; ring
          have hpref : (0:ℝ) ≤ 4 * (1/4:ℝ) ^ b := by positivity
          calc ∑ ρ ∈ fib, G ρ
              = ∑ ρ ∈ fib, (4 * (1/4) ^ b) * (D (ρ : ℂ) : ℝ) := Finset.sum_congr rfl hshell_eq
            _ = (4 * (1/4) ^ b) * ((∑ ρ ∈ fib, D (ρ : ℂ) : ℤ) : ℝ) := by
                rw [← Finset.mul_sum]; push_cast; ring
            _ ≤ (4 * (1/4) ^ b) * (C * (1 + r) * Real.log (2 + r)) :=
                mul_le_mul_of_nonneg_left hmass hpref
            _ = 4 * bnd b := by simp only [hbnddef, hrdef]; ring
      _ = 4 * ∑ b ∈ uf.image (fun ρ : ↥D.support => xiShell (ρ : ℂ)), bnd b := by rw [Finset.mul_sum]
      _ ≤ 4 * B := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [hBdef]
          exact hbndsum.sum_le_tsum _ (fun i _ => hbndnn i)

end RHTower
