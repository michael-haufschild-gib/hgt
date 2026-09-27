import GaloisForLFunctions.HTGeometry.FirstOrderRelationLaurentBranch
import GaloisForLFunctions.HTGeometry.HahnDilation
import GaloisForLFunctions.HTGeometry.LaurentHasLead

/-!
# The Wiman top-symbol root in an arbitrary Laurent layer

Reduction I produces a root of the complete top symbol `Q(U,T)` of a first-order relation over the
complex Laurent field, at `U = t^(-e)`, with leading coefficient the prescribed Wiman edge root and
exponent `k < e` (the positive Wiman charge).  Because `Q` has polynomial coefficients in `U`, this
root survives every base change `t ↦ t^m` into any Laurent field `K((t))` over `ℂ`: it stays a root
of `Q(t^(-e m),·)` with exponent `m k` and the same leading coefficient.

That is the reason the cascade's Wiman leads can be chosen compatibly at every level: the root at
level `j+1` is fixed by the level-`j` Laurent coordinate alone.
-/

open HahnSeries Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Exponent dilation -/

/-- Multiplication of exponents by `m`. -/
def mulExponent (m : ℕ) : ℤ →+ ℤ := AddMonoidHom.mulLeft (m : ℤ)

@[simp] theorem mulExponent_apply (m : ℕ) (n : ℤ) : mulExponent m n = m * n := rfl

theorem mulExponent_injective {m : ℕ} (hm : m ≠ 0) : Function.Injective (mulExponent m) := by
  intro a b h
  simp only [mulExponent_apply] at h
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hm) h

theorem mulExponent_le_iff {m : ℕ} (hm : m ≠ 0) (g g' : ℤ) :
    mulExponent m g ≤ mulExponent m g' ↔ g ≤ g' := by
  simp only [mulExponent_apply]
  exact mul_le_mul_iff_right₀ (by exact_mod_cast Nat.pos_of_ne_zero hm)

variable (K : Type) [Field K] [Algebra ℂ K]

/-- Base change of a complex Laurent series along `t ↦ tᵐ` into `K((t))`. -/
def laurentBaseChange (m : ℕ) (hm : m ≠ 0) : LaurentSeries ℂ →+* LaurentSeries K :=
  (embDomainRingHom (mulExponent m) (mulExponent_injective hm) (mulExponent_le_iff hm)).comp
    (hahnMapRingHom (Γ := ℤ) (algebraMap ℂ K))

variable {K}

theorem laurentBaseChange_coeff_mul {m : ℕ} (hm : m ≠ 0) (x : LaurentSeries ℂ) (n : ℤ) :
    (laurentBaseChange K m hm x).coeff ((m : ℤ) * n) = algebraMap ℂ K (x.coeff n) := by
  exact (HahnSeries.embDomain_coeff (a := n)).trans (coeff_hahnMapRingHom _ _ _)

theorem laurentBaseChange_coeff_of_not_mem {m : ℕ} (hm : m ≠ 0) (x : LaurentSeries ℂ) (k : ℤ)
    (hk : ∀ n : ℤ, (m : ℤ) * n ≠ k) :
    (laurentBaseChange K m hm x).coeff k = 0 := by
  change (embDomain _ (hahnMapRingHom (Γ := ℤ) (algebraMap ℂ K) x)).coeff k = 0
  apply embDomain_notin_range
  rintro ⟨n, hn⟩
  exact hk n hn

theorem laurentBaseChange_algebraMap {m : ℕ} (hm : m ≠ 0) (c : ℂ) :
    laurentBaseChange K m hm (algebraMap ℂ (LaurentSeries ℂ) c) =
      algebraMap ℂ (LaurentSeries K) c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
    HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]
  change embDomainRingHom _ _ _ ((hahnMapRingHom (Γ := ℤ) (algebraMap ℂ K))
    (HahnSeries.C _)) = _
  rw [show (hahnMapRingHom (Γ := ℤ) (algebraMap ℂ K)) (HahnSeries.C ((algebraMap ℂ ℂ) c)) =
      HahnSeries.C (algebraMap ℂ K c) by
    ext n
    rw [coeff_hahnMapRingHom, HahnSeries.C_apply, HahnSeries.C_apply, coeff_single,
      coeff_single]
    split_ifs <;> simp, embDomainRingHom_C]

theorem laurentBaseChange_single {m : ℕ} (hm : m ≠ 0) (e : ℤ) (c : ℂ) :
    laurentBaseChange K m hm (single e c) = single ((m : ℤ) * e) (algebraMap ℂ K c) := by
  ext k
  by_cases hk : ∃ n : ℤ, (m : ℤ) * n = k
  · obtain ⟨n, rfl⟩ := hk
    rw [laurentBaseChange_coeff_mul, coeff_single, coeff_single]
    by_cases hne : n = e
    · subst hne; simp
    · rw [if_neg hne, if_neg, map_zero]
      intro h
      exact hne (mul_left_cancel₀ (Int.natCast_ne_zero.mpr hm) h)
  · push Not at hk
    rw [laurentBaseChange_coeff_of_not_mem hm _ _ hk, coeff_single, if_neg (fun h => hk e h.symm)]

theorem HasLead.laurentBaseChange {m : ℕ} (hm : m ≠ 0) {x : LaurentSeries ℂ} {d : ℤ} {c : ℂ}
    (hx : HasLead x d c) :
    HasLead (laurentBaseChange K m hm x) ((m : ℤ) * d) (algebraMap ℂ K c) := by
  have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  refine ⟨fun k hk => ?_, by rw [laurentBaseChange_coeff_mul, hx.2]⟩
  by_cases hkm : ∃ n : ℤ, (m : ℤ) * n = k
  · obtain ⟨n, rfl⟩ := hkm
    rw [laurentBaseChange_coeff_mul, hx.1 n (lt_of_mul_lt_mul_left hk hmpos.le), map_zero]
  · push Not at hkm
    exact laurentBaseChange_coeff_of_not_mem hm _ _ hkm

/-! ## The top symbol under base change -/

/-- A ring map compatible with the complex structures carries the top symbol at `u` to the top
symbol at the image of `u`. -/
theorem topSymbolAt_map {F F' : Type} [Field F] [Algebra ℂ F] [Field F'] [Algebra ℂ F']
    (φ : F →+* F') (hφ : ∀ c : ℂ, φ (algebraMap ℂ F c) = algebraMap ℂ F' c)
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ) (u : F) :
    topSymbolAt S A d (φ u) = (topSymbolAt S A d u).map φ := by
  have hcomp : φ.comp (algebraMap ℂ F) = algebraMap ℂ F' := RingHom.ext hφ
  rw [topSymbolAt, topSymbolAt, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  congr 2
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp]

/-- The complex Laurent top-symbol value of the corpus is evaluation of `topSymbolAt`. -/
theorem firstOrderTopSymbolLaurentValue_eq_eval (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ)
    (d : ℕ) (U T : LaurentSeries ℂ) :
    firstOrderTopSymbolLaurentValue S A d U T = (topSymbolAt S A d U).eval T := by
  rw [firstOrderTopSymbolLaurentValue, topSymbolAt, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  rw [Finset.sum_subset (Polynomial.supp_subset_range_natDegree_succ)]
  · apply Finset.sum_congr rfl
    intro n _
    rw [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  · intro n _ hn
    rw [Polynomial.notMem_support_iff.mp hn]
    simp

/-- At a nonzero Laurent pole, the evaluation of a nonzero polynomial is nonzero. -/
theorem aeval_single_ne_zero (p : Polynomial ℂ) (hp : p ≠ 0) (e : ℤ) (he : e ≠ 0) :
    Polynomial.aeval (single (-e) (1 : K)) p ≠ 0 := by
  classical
  intro hzero
  have hcoeff := congrArg (fun h : LaurentSeries K => h.coeff ((p.natDegree : ℤ) * -e)) hzero
  simp only [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, HahnSeries.coeff_zero,
    Algebra.smul_def] at hcoeff
  rw [Finset.sum_eq_single p.natDegree] at hcoeff
  · rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, laurent_single_one_pow,
      coeff_single_same, smul_eq_mul, mul_one, Polynomial.coeff_natDegree] at hcoeff
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
      ((algebraMap ℂ K).injective (by rw [hcoeff, map_zero]))
  · intro n _ hn
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, laurent_single_one_pow,
      coeff_single_of_ne, smul_zero]
    intro h
    have h' := mul_right_cancel₀ (neg_ne_zero.mpr he) h
    exact hn (by exact_mod_cast h'.symm)
  · intro hn
    exact absurd (Finset.self_mem_range_succ p.natDegree) hn

/-- The top symbol is a nonzero polynomial at a nonzero Laurent pole, as soon as the top face is
inhabited. -/
theorem topSymbolAt_single_ne_zero (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (i₀ : ℕ × ℕ) (hi₀ : i₀ ∈ firstOrderTopNewtonFace S A d) (e : ℤ) (he : e ≠ 0) :
    topSymbolAt S A d (single (-e) (1 : K)) ≠ 0 := by
  classical
  intro hzero
  have hcoeff := congrArg (fun P : Polynomial (LaurentSeries K) => P.coeff i₀.2) hzero
  simp only [topSymbolAt, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single_of_mem i₀ hi₀] at hcoeff
  · rw [if_pos rfl, mul_one] at hcoeff
    exact aeval_single_ne_zero (A i₀) (Finset.mem_filter.mp hi₀).2.2 e he hcoeff
  · intro i hi hne
    rw [if_neg, mul_zero]
    intro hsnd
    apply hne
    apply Prod.ext
    · have hiDeg := (Finset.mem_filter.mp hi).2.1
      have hi₀Deg := (Finset.mem_filter.mp hi₀).2.1
      omega
    · exact hsnd.symm

/-! ## The Wiman root in every Laurent layer -/

/-- **The Wiman top-symbol root over the complex Laurent field.**  At `U = t^(-e)` the top symbol
has a root with leading coefficient the Wiman edge root in degree `k < e`. -/
theorem exists_wiman_topSymbol_laurent_root {f : ℂ → ℂ}
    (data : EntireFirstOrderWimanInitialData f) :
    ∃ (e : ℕ) (_ : e ≠ 0) (k : ℤ) (τ : LaurentSeries ℂ),
      (topSymbolAt data.indexSupport data.coeff data.totalDegree
        (single (-(e : ℤ)) (1 : ℂ))).IsRoot τ ∧
      HasLead τ k data.root ∧ k < e := by
  obtain ⟨M, a, q, N, hN, z, hq, hp, hz, htop⟩ := exists_entireFirstOrderWiman_topSymbolLaurentRoot data
  refine ⟨N * q, Nat.mul_ne_zero hN hq, -((N * M : ℕ) : ℤ) + ((N * a : ℕ) : ℤ),
    single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
      algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z),
    ?_, ?_, ?_⟩
  · rw [Polynomial.IsRoot, ← firstOrderTopSymbolLaurentValue_eq_eval]
    exact_mod_cast htop
  · have hs : HasLead (single (-((N * M : ℕ) : ℤ)) (1 : ℂ) : LaurentSeries ℂ)
        (-((N * M : ℕ) : ℤ)) 1 :=
      ⟨fun k hk => by rw [coeff_single_of_ne (by omega)], by rw [coeff_single_same]⟩
    have hx : HasLead (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
        ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z)) ((N * a : ℕ) : ℤ) data.root := by
      refine ⟨fun k hk => ?_, ?_⟩
      · change ((((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z : PowerSeries ℂ)) :
          LaurentSeries ℂ).coeff k = 0
        rw [PowerSeries.coeff_coe]
        split_ifs with h
        · rfl
        · rw [PowerSeries.coeff_X_pow_mul', if_neg]
          omega
      · change ((((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z : PowerSeries ℂ)) :
          LaurentSeries ℂ).coeff ((N * a : ℕ) : ℤ) = _
        rw [PowerSeries.coeff_coe, if_neg (by omega), Int.natAbs_natCast,
          PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
          PowerSeries.coeff_zero_eq_constantCoeff_apply, hz]
    simpa using hs.mul hx
  · have hcharge := data.charge_pos
    rw [hp] at hcharge
    have hqpos : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    have hlt : (a : ℚ) - M < q := by
      have h := hcharge
      rw [show ((((M : ℚ) - a) / q : ℚ) : ℝ) + 1 = (((M - a + q) / q : ℚ) : ℝ) by
        push_cast; field_simp] at h
      have h' : (0 : ℚ) < (M - a + q) / q := by exact_mod_cast h
      have := (div_pos_iff_of_pos_right hqpos).mp h'
      linarith
    have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hlt' : (a : ℤ) - M < q := by exact_mod_cast hlt
    push_cast
    nlinarith

end

end GaloisForLFunctions.HTGeometry
