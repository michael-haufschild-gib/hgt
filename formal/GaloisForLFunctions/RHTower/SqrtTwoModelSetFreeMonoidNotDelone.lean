import GaloisForLFunctions.RHTower.SqrtTwoPrimeSumBound
import GaloisForLFunctions.RHTower.FreeMonoidEulerBounds

/-!
# Free multiplicative monoids in the `ℤ[√2]` model set are not relatively dense

Let `g : ι → ℤ[√2]` take values in the window `{θ : θ > 1, |θ̄| ≤ 1}` and generate a free
multiplicative monoid: `f ↦ Π g_i^{f_i}` is injective on `ι →₀ ℕ`. Then the monoid is not
relatively dense in `[1, ∞)`. No `R` puts one of its elements in every interval `[x, x+R]`.

So no arithmetical Delone semigroup (unique factorization with bounded gaps) lies inside the
window model set of `ℤ[√2]`. This is the quadratic Meyer case of Lagarias's question on Delone
Beurling integers.

Proof, for `1 < σ ≤ 2`:
* Relative density gives a finite family with `Σ θ^{−σ} ≥ c/(σ−1)`.
* The finite Euler bound gives `Σ θ^{−σ} ≤ Π (1 − g_i^{−σ})^{−1}`.
* After removing at most one generator, the prime transversal and the window defect give
  `log Π ≤ (1 − κ) log(1/(σ−1)) + D`, `κ > 0`.
* Hence `(σ−1)^{−κ}` is bounded, which fails as `σ → 1⁺`.
-/

noncomputable section

namespace RHTower.SqrtTwo

open UniqueFactorizationMonoid

variable {ι : Type*} {g : ι → ℤ√2}

theorem emb_prodPow_rpow_eq (hg : ∀ i, 0 < emb (g i)) (f : ι →₀ ℕ) {F : Finset ι}
    (hF : f.support ⊆ F) (σ : ℝ) :
    emb (prodPow g f) ^ (-σ) = ∏ i ∈ F, (emb (g i) ^ (-σ)) ^ f i := by
  have h1 : emb (prodPow g f) = ∏ i ∈ F, emb (g i) ^ f i := by
    rw [prodPow, map_finsuppProd, Finsupp.prod]
    simp only [map_pow]
    exact Finset.prod_subset hF fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  rw [h1, ← Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (hg i).le _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (hg i).le,
    ← Real.rpow_mul (hg i).le, mul_comm]

theorem one_le_prod_of_one_le_real {κ : Type*} (s : Finset κ) (f : κ → ℝ)
    (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  have := Finset.prod_le_prod (s := s) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) h1
  simpa using this

theorem prod_le_prod_of_subset_real {κ : Type*} [DecidableEq κ] {s t : Finset κ} (hst : s ⊆ t)
    (f : κ → ℝ) (h1 : ∀ i ∈ t, 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff hst]
  have hA : 1 ≤ ∏ i ∈ t \ s, f i :=
    one_le_prod_of_one_le_real _ _ fun i hi => h1 i (Finset.mem_sdiff.mp hi).1
  have hB : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => by linarith [h1 i (hst hi)]
  nlinarith

/-- **Free monoids in the window of `ℤ[√2]` are not relatively dense.** -/
theorem not_relativelyDense_of_free (g : ι → ℤ√2)
    (hwin : ∀ i, 1 < emb (g i) ∧ |emb (star (g i))| ≤ 1)
    (hfree : Function.Injective (prodPow g)) (R : ℝ) :
    ¬ ∀ x : ℝ, 1 ≤ x → ∃ f : ι →₀ ℕ, x ≤ emb (prodPow g f) ∧ emb (prodPow g f) ≤ x + R := by
  classical
  intro hR
  have hg : ∀ i, 0 < emb (g i) := fun i => by linarith [(hwin i).1]
  obtain ⟨S, hS, τ, hτinj, hτmem⟩ := exists_prime_transversal hg hfree
  obtain ⟨κ, hκ, D, hD⟩ := exists_prime_sum_bound
  have hSfin : S.Finite := hS.finite
  set MS : ℝ := ∏ i ∈ hSfin.toFinset, (1 - (emb (g i))⁻¹)⁻¹ with hMS
  have hfac1 : ∀ i, 1 ≤ (1 - (emb (g i))⁻¹)⁻¹ := by
    intro i
    have h1 := (hwin i).1
    have hpos : 0 < 1 - (emb (g i))⁻¹ := by
      have : (emb (g i))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
      linarith
    rw [one_le_inv₀ hpos]
    have : 0 < (emb (g i))⁻¹ := inv_pos.mpr (hg i)
    linarith
  have hMS1 : 1 ≤ MS := one_le_prod_of_one_le_real _ _ fun i _ => hfac1 i
  set cR : ℝ := 1 / (18 * (max R 1) ^ 2) with hcR
  have hcR0 : 0 < cR := by rw [hcR]; positivity
  -- the key inequality
  have key : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      cR * (1 / (σ - 1)) ≤ MS * Real.exp ((1 - κ) * Real.log (1 / (σ - 1)) + D) := by
    intro σ hσ hσ2
    obtain ⟨Φ, hΦ⟩ := FreeMonoidEuler.exists_sum_rpow_ge (fun f => emb (prodPow g f)) hR hσ hσ2
    set F := Φ.biUnion fun f => f.support with hF
    set e : ι → ℝ := fun i => emb (g i) ^ (-σ) with he
    have he0 : ∀ i, 0 ≤ e i := fun i => Real.rpow_nonneg (hg i).le _
    have he1 : ∀ i, e i < 1 := fun i =>
      Real.rpow_lt_one_of_one_lt_of_neg (hwin i).1 (by linarith)
    have hsupp : ∀ f ∈ Φ, f.support ⊆ F := fun f hf => Finset.subset_biUnion_of_mem _ hf
    have hsumΦ : ∑ f ∈ Φ, emb (prodPow g f) ^ (-σ) = ∑ f ∈ Φ, ∏ i ∈ F, e i ^ f i :=
      Finset.sum_congr rfl fun f hf => emb_prodPow_rpow_eq hg f (hsupp f hf) σ
    have hEuler := FreeMonoidEuler.sum_prod_pow_le_prod_inv e he0 he1 F Φ hsupp
    -- split off the removed generators
    rw [← Finset.prod_filter_mul_prod_filter_not F (· ∈ S)] at hEuler
    have hSpart : ∏ i ∈ F.filter (· ∈ S), (1 - e i)⁻¹ ≤ MS := by
      calc ∏ i ∈ F.filter (· ∈ S), (1 - e i)⁻¹
          ≤ ∏ i ∈ F.filter (· ∈ S), (1 - (emb (g i))⁻¹)⁻¹ := by
            refine Finset.prod_le_prod (fun i _ => inv_nonneg.mpr (by linarith [he1 i]))
              fun i _ => ?_
            have hle : e i ≤ (emb (g i))⁻¹ := by
              rw [he]; simp only
              rw [← Real.rpow_neg_one]
              exact Real.rpow_le_rpow_of_exponent_le (hwin i).1.le (by linarith)
            have hpos : 0 < 1 - (emb (g i))⁻¹ := by
              have : (emb (g i))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (hwin i).1
              linarith
            exact inv_anti₀ hpos (by linarith)
        _ ≤ MS := by
            refine prod_le_prod_of_subset_real ?_ _ fun i _ => hfac1 i
            intro i hi
            rw [Set.Finite.mem_toFinset]; exact (Finset.mem_filter.mp hi).2
    -- the remaining generators have small weights
    have hbound : ∀ i (hi : i ∉ S), e i ≤
        ((((τ ⟨i, hi⟩).norm.natAbs : ℕ) : ℝ) ^ (-σ)) * phiW (τ ⟨i, hi⟩) :=
      fun i hi => emb_rpow_neg_le (hg i) (hwin i).2 (hτmem ⟨i, hi⟩) hσ.le
    have hprime : ∀ j : {i // i ∉ S}, Prime (τ j) ∧ normalize (τ j) = τ j := fun j =>
      ⟨prime_of_normalized_factor _ (hτmem j), normalize_normalized_factor _ (hτmem j)⟩
    have hN2 : ∀ j : {i // i ∉ S}, (2 : ℝ) ≤ (((τ j).norm.natAbs : ℕ) : ℝ) := fun j => by
      exact_mod_cast two_le_natAbs_norm (hprime j).1.ne_zero (hprime j).1.not_unit
    have hsmall : ∀ i (hi : i ∉ S), e i ≤ (((τ ⟨i, hi⟩).norm.natAbs : ℕ) : ℝ)⁻¹ := by
      intro i hi
      have hN := hN2 ⟨i, hi⟩
      refine (hbound i hi).trans ?_
      calc ((((τ ⟨i, hi⟩).norm.natAbs : ℕ) : ℝ) ^ (-σ)) * phiW (τ ⟨i, hi⟩)
          ≤ ((((τ ⟨i, hi⟩).norm.natAbs : ℕ) : ℝ) ^ (-σ)) * 1 :=
            mul_le_mul_of_nonneg_left (phiW_le_one _) (Real.rpow_nonneg (by linarith) _)
        _ ≤ ((((τ ⟨i, hi⟩).norm.natAbs : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
            rw [mul_one]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = (((τ ⟨i, hi⟩).norm.natAbs : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _
    have hhalf : ∀ i ∈ F.filter (· ∉ S), e i ≤ 1 / 2 := by
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have hN := hN2 ⟨i, hi'⟩
      refine (hsmall i hi').trans ?_
      rw [one_div]; exact inv_anti₀ (by norm_num) hN
    have hrest := FreeMonoidEuler.prod_inv_le_exp_sum (F.filter (· ∉ S)) e hhalf
    -- the exponent
    have hexp : ∑ i ∈ F.filter (· ∉ S), (e i + 2 * e i ^ 2) ≤
        (1 - κ) * Real.log (1 / (σ - 1)) + D := by
      set Fsub : Finset {i // i ∉ S} := F.subtype (· ∉ S) with hFsub
      rw [← Finset.sum_subtype_eq_sum_filter (fun i => e i + 2 * e i ^ 2)]
      set G : ℤ√2 → ℝ := fun π => ((π.norm.natAbs : ℕ) : ℝ) ^ (-σ) * phiW π +
        2 * ((π.norm.natAbs : ℕ) : ℝ) ^ (-(2 : ℝ)) with hG
      calc ∑ j ∈ Fsub, (e j.1 + 2 * e j.1 ^ 2)
          ≤ ∑ j ∈ Fsub, G (τ j) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 := hbound j.1 j.2
            have h2 := hsmall j.1 j.2
            have hN := hN2 j
            have hsq : e j.1 ^ 2 ≤ (((τ j).norm.natAbs : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
              rw [Real.rpow_neg (by linarith), Real.rpow_two]
              have := he0 j.1
              calc e j.1 ^ 2 ≤ ((((τ j).norm.natAbs : ℕ) : ℝ)⁻¹) ^ 2 := by gcongr
                _ = ((((τ j).norm.natAbs : ℕ) : ℝ) ^ 2)⁻¹ := by rw [inv_pow]
            simp only [hG]
            linarith
        _ = ∑ π ∈ Fsub.image τ, G π := (Finset.sum_image fun x _ y _ h => hτinj h).symm
        _ ≤ (1 - κ) * Real.log (1 / (σ - 1)) + D := by
            apply hD σ hσ hσ2
            intro π hπ
            obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hπ
            exact hprime j
    have hΦ' : cR * (1 / (σ - 1)) ≤ ∑ f ∈ Φ, emb (prodPow g f) ^ (-σ) := by
      refine le_trans (le_of_eq ?_) hΦ
      rw [hcR]; field_simp
    calc cR * (1 / (σ - 1)) ≤ ∑ f ∈ Φ, emb (prodPow g f) ^ (-σ) := hΦ'
      _ = ∑ f ∈ Φ, ∏ i ∈ F, e i ^ f i := hsumΦ
      _ ≤ (∏ i ∈ F.filter (· ∈ S), (1 - e i)⁻¹) * ∏ i ∈ F.filter (· ∉ S), (1 - e i)⁻¹ := hEuler
      _ ≤ MS * Real.exp (∑ i ∈ F.filter (· ∉ S), (e i + 2 * e i ^ 2)) := by
          apply mul_le_mul hSpart hrest
          · exact Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by linarith [he1 i])
          · linarith
      _ ≤ MS * Real.exp ((1 - κ) * Real.log (1 / (σ - 1)) + D) := by
          gcongr
  -- contradiction as `σ → 1⁺`
  set K : ℝ := MS * Real.exp D / cR with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  set t : ℝ := min (1 / 2) ((K + 1) ^ (-(1 / κ))) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have hkey := key (1 + t) (by linarith) (by linarith)
  rw [add_sub_cancel_left] at hkey
  set u : ℝ := 1 / t with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hexpu : Real.exp ((1 - κ) * Real.log u + D) = Real.exp D * u ^ (1 - κ) := by
    rw [Real.exp_add, Real.rpow_def_of_pos hu0, mul_comm (Real.log u), mul_comm]
  rw [hexpu] at hkey
  -- `cR u ≤ MS e^D u^{1−κ}` gives `u^κ ≤ K`
  have hupow : u ^ κ ≤ K := by
    have hu1κ : 0 < u ^ (1 - κ) := Real.rpow_pos_of_pos hu0 _
    have hsplit : u = u ^ κ * u ^ (1 - κ) := by
      rw [← Real.rpow_add hu0]; simp
    rw [hK, le_div_iff₀ hcR0]
    have : cR * (u ^ κ * u ^ (1 - κ)) ≤ MS * (Real.exp D * u ^ (1 - κ)) := by
      rw [← hsplit]; exact hkey
    have h2 : u ^ κ * cR * u ^ (1 - κ) ≤ MS * Real.exp D * u ^ (1 - κ) := by nlinarith
    exact le_of_mul_le_mul_right h2 hu1κ
  -- but `u ≥ (K+1)^{1/κ}`
  have hu_big : (K + 1) ^ (1 / κ) ≤ u := by
    rw [hu]
    have hpos : 0 < (K + 1) ^ (1 / κ) := Real.rpow_pos_of_pos (by linarith) _
    have htle : t ≤ ((K + 1) ^ (1 / κ))⁻¹ := by
      rw [← Real.rpow_neg (by linarith)]; exact min_le_right _ _
    have := (le_inv_comm₀ ht0 hpos).mp htle
    simpa [one_div] using this
  have hbig : K + 1 ≤ u ^ κ := by
    calc K + 1 = ((K + 1) ^ (1 / κ)) ^ κ := by
          rw [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hκ.ne', Real.rpow_one]
      _ ≤ u ^ κ := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hu_big hκ.le
  linarith

end RHTower.SqrtTwo
