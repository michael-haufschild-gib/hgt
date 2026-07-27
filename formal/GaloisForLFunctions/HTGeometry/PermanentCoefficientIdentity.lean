import GaloisForLFunctions.HTGeometry.DifferentialMonomialCoefficient
import GaloisForLFunctions.HTGeometry.SuperIncreasingSourceUnique
import GaloisForLFunctions.HTGeometry.PermanentDistinctSymbol
import GaloisForLFunctions.HTGeometry.MvPolynomialInfiniteEval
import GaloisForLFunctions.HTGeometry.IterateDerivativeFalling

/-!
# The distinct-index coefficient is a permanent

At `r` distinct source scales `bnat Mᵢ` the coefficient of a differential monomial `∏ₜ f^{(μₜ)}`
of a tail-supported superlacunary series is a **permanent** over those scales.  Unlike the balanced
index (all sources equal, a single surviving antidiagonal point → the weight polynomial), the
distinct index has `r!` surviving antidiagonal points — one per assignment `π` of the `r` factors to
the `r` scales — and they sum to `(∏ᵢ coeff (bnat Mᵢ) f) · permSymbol`.

The `coeff_prod_iterate_derivative_of_subset` lemma isolates the surviving set; `multiset_source_unique`
identifies it as exactly the permutation orbit of the balanced assignment.

Because the permanent symbol `permSymbolPoly` lives over `ℤ` while a differential-algebraic relation
has complex coefficients, the survival theorems are proved for complex coefficients acting on the
cast symbols `(permSymbolPoly ν).map (ℤ → ℂ)`; the integer statements are the cast specialisations.
-/

open PowerSeries Finset

namespace GaloisForLFunctions

variable {R : Type*} [CommSemiring R]

/-- **Coefficient supported on a surviving subset.**  If every antidiagonal index outside a subset
`T` kills the differential-monomial product (some factor reads a zero coefficient of `f`), then the
`N`-th coefficient is the sum over `T` alone.  Generalises `coeff_prod_iterate_derivative_of_unique`
from one surviving index to the full permutation orbit. -/
theorem coeff_prod_iterate_derivative_of_subset {r : ℕ} (j : Fin r → ℕ) (f : R⟦X⟧) (N : ℕ)
    (T : Finset (Fin r →₀ ℕ)) (hT : T ⊆ (Finset.univ : Finset (Fin r)).finsuppAntidiag N)
    (hvanish : ∀ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N, l ∉ T →
      ∃ t, coeff (l t + j t) f = 0) :
    coeff N (∏ t, (⇑(d⁄dX R))^[j t] f)
      = ∑ l ∈ T, ∏ t, coeff (l t + j t) f * ∏ i ∈ Finset.range (j t), ((l t + 1 + i : ℕ) : R) := by
  rw [coeff_prod_iterate_derivative]
  symm
  apply Finset.sum_subset hT
  intro l hl hnotT
  obtain ⟨t, ht⟩ := hvanish l hl hnotT
  exact Finset.prod_eq_zero (Finset.mem_univ t) (by rw [ht, zero_mul])

/-- **Permutation from equal image multisets.**  If two index maps `n, M : Fin r → ℕ` have the same
value multiset and `M` is injective, then `n` is a permutation of `M`: there is `σ` with
`n = M ∘ σ`.  This turns the multiset uniqueness of the source scales into an explicit assignment. -/
theorem exists_perm_of_map_eq {r : ℕ} (n M : Fin r → ℕ) (hM : Function.Injective M)
    (hmap : Multiset.map n Finset.univ.val = Multiset.map M Finset.univ.val) :
    ∃ σ : Equiv.Perm (Fin r), ∀ t, n t = M (σ t) := by
  classical
  have hmem : ∀ t, ∃ s, M s = n t := by
    intro t
    have h1 : n t ∈ Multiset.map n Finset.univ.val :=
      Multiset.mem_map.mpr ⟨t, Finset.mem_univ_val t, rfl⟩
    rw [hmap] at h1
    obtain ⟨s, _, hs⟩ := Multiset.mem_map.mp h1
    exact ⟨s, hs⟩
  choose g hg using hmem
  -- `n` is injective: its value multiset equals the nodup multiset of the injective `M`
  have hnodupM : (Multiset.map M Finset.univ.val).Nodup :=
    Finset.univ.nodup.map hM
  have hnodupn : (Multiset.map n Finset.univ.val).Nodup := by rw [hmap]; exact hnodupM
  have hninj : Function.Injective n := by
    intro a b hab
    exact Multiset.inj_on_of_nodup_map hnodupn a (Finset.mem_univ_val a) b
      (Finset.mem_univ_val b) hab
  have hginj : Function.Injective g := by
    intro a b hab
    apply hninj
    rw [← hg a, ← hg b, hab]
  refine ⟨Equiv.ofBijective g ((Finite.injective_iff_bijective).mp hginj), fun t => ?_⟩
  rw [Equiv.ofBijective_apply]
  exact (hg t).symm

open Nat in
/-- **The distinct-index coefficient is a permanent.**  For a tail-supported series on the
super-increasing gap set, at the distinct-scale index `∑ₜ (bnat (M t) − μ t)` the coefficient of the
differential monomial `∏ₜ f^{(μₜ)}` equals `(∏ᵢ coeff (bnat Mᵢ) f)` times the permanent
`∑_π ∏ₜ descFactorial (bnat (M (π t))) (μ t)`. -/
theorem coeff_distinct_index_eq_permanent {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ}
    (hb0 : 0 < bnat 0) (hstair : ∀ n, r * bnat n < bnat (n + 1)) (hbnatinj : Function.Injective bnat)
    (μ : Fin r → ℕ) {f : ℂ⟦X⟧}
    (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (M : Fin r → ℕ) (hMinj : Function.Injective M) (hbig : ∀ i t, μ t ≤ bnat (M i)) :
    coeff (∑ t, (bnat (M t) - μ t)) (∏ t, (⇑(d⁄dX ℂ))^[μ t] f)
      = (∏ i, coeff (bnat (M i)) f)
        * ∑ π : Equiv.Perm (Fin r), ∏ t, (Nat.descFactorial (bnat (M (π t))) (μ t) : ℂ) := by
  classical
  set N := ∑ t, (bnat (M t) - μ t) with hN
  have hsumπ : ∀ π : Equiv.Perm (Fin r), ∑ t, (bnat (M (π t)) - μ t) = N := by
    intro π
    rw [hN, Finset.sum_tsub_distrib Finset.univ (fun t _ => hbig (π t) t),
      Finset.sum_tsub_distrib Finset.univ (fun t _ => hbig t t)]
    congr 1
    exact Equiv.sum_comp π (fun i => bnat (M i))
  set lPt : Equiv.Perm (Fin r) → (Fin r →₀ ℕ) :=
    fun π => Finsupp.onFinset Finset.univ (fun t => bnat (M (π t)) - μ t)
      (fun a _ => Finset.mem_univ a) with hlPtdef
  have hlPtApp : ∀ π t, lPt π t = bnat (M (π t)) - μ t := by intro π t; rw [hlPtdef]; simp
  have hlPtSource : ∀ π t, lPt π t + μ t = bnat (M (π t)) := by
    intro π t; rw [hlPtApp π t, Nat.sub_add_cancel (hbig (π t) t)]
  have hlPtMem : ∀ π, lPt π ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N := by
    intro π
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by rw [Finset.sum_congr rfl (fun t _ => hlPtApp π t)]; exact hsumπ π,
      Finsupp.support_onFinset_subset⟩
  have hlPtInj : Function.Injective lPt := by
    intro π₁ π₂ h
    ext t
    have h1 : lPt π₁ t + μ t = lPt π₂ t + μ t := by rw [h]
    rw [hlPtSource, hlPtSource] at h1
    exact congrArg _ (hMinj (hbnatinj h1))
  set T : Finset (Fin r →₀ ℕ) := Finset.image lPt Finset.univ with hTdef
  have hvanish : ∀ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N, l ∉ T →
      ∃ t, coeff (l t + μ t) f = 0 := by
    intro l hl hlnotT
    by_contra hcon
    push Not at hcon
    apply hlnotT
    choose n hn using fun t => hsupp (l t + μ t) (hcon t)
    have hsumN : ∑ t, l t = N := (Finset.mem_finsuppAntidiag.mp hl).1
    have hmasseq : (Multiset.map bnat (Finset.univ.val.map n)).sum
        = (Multiset.map bnat (Finset.univ.val.map M)).sum := by
      rw [Multiset.map_map, Multiset.map_map]
      show (∑ t, bnat (n t)) = ∑ t, bnat (M t)
      rw [Finset.sum_congr rfl (fun t _ => (hn t).symm), Finset.sum_add_distrib, hsumN]
      have : ∑ t, bnat (M t) = ∑ t, (bnat (M t) - μ t) + ∑ t, μ t := by
        rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun t _ => Nat.sub_add_cancel (hbig t t))]
      rw [this, hN]
    have hmapeq : Finset.univ.val.map n = Finset.univ.val.map M := by
      apply multiset_source_unique hmono hb0 hstair
      · simp
      · simp
      · exact Finset.univ.nodup.map hMinj
      · exact hmasseq
    obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq n M hMinj hmapeq
    rw [hTdef, Finset.mem_image]
    refine ⟨σ, Finset.mem_univ σ, ?_⟩
    ext t
    rw [hlPtApp]
    have hsrc : l t + μ t = bnat (M (σ t)) := by rw [hn t, hσ t]
    omega
  rw [coeff_prod_iterate_derivative_of_subset μ f N T (fun l hl => by
      rw [hTdef, Finset.mem_image] at hl; obtain ⟨π, _, rfl⟩ := hl; exact hlPtMem π) hvanish]
  -- sum over the image is a sum over permutations
  rw [Finset.sum_image (fun π₁ _ π₂ _ h => hlPtInj h)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  -- the permutation term
  have hval : ∀ t, coeff (lPt π t + μ t) f
        * ∏ i ∈ Finset.range (μ t), ((lPt π t + 1 + i : ℕ) : ℂ)
      = coeff (bnat (M (π t))) f * (Nat.descFactorial (bnat (M (π t))) (μ t) : ℂ) := by
    intro t
    rw [← Nat.cast_prod, prod_range_succ_add_eq_descFactorial, hlPtSource π t]
  rw [Finset.prod_congr rfl (fun t _ => hval t), Finset.prod_mul_distrib,
    show (∏ t, coeff (bnat (M (π t))) f) = ∏ i, coeff (bnat (M i)) f from
      Equiv.prod_comp π (fun i => coeff (bnat (M i)) f)]

/-- **Evaluation of the permanent symbol is the permanent.**  Evaluating `permSymbolPoly μ` at
integer scales `s` produces exactly the falling-factorial permanent over those scales. -/
theorem eval_permSymbolPoly {r : ℕ} (μ : Fin r → ℕ) (s : Fin r → ℕ) :
    (MvPolynomial.eval (fun i => (s i : ℤ))) (permSymbolPoly μ)
      = ∑ π : Equiv.Perm (Fin r), ∏ t, (Nat.descFactorial (s (π t)) (μ t) : ℤ) := by
  classical
  have heval : ∀ (j : Fin r) (p : Polynomial ℤ),
      MvPolynomial.eval (fun i => (s i : ℤ)) (Polynomial.aeval (MvPolynomial.X j) p)
        = Polynomial.eval ((s j : ℤ)) p := by
    intro j p
    induction p using Polynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
    | monomial n a _ => simp
  rw [permSymbolPoly, map_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro t _
  rw [heval, descPochhammer_eval_eq_descFactorial]

/-- **Infinite-grid nonvanishing over a field.**  A nonzero `MvPolynomial (Fin r) 𝕜` is nonzero at
some injective tuple valued in any infinite subset of `𝕜`. -/
theorem exists_injective_eval_ne_zero_field {𝕜 : Type*} [Field 𝕜] :
    ∀ {r : ℕ} (P : MvPolynomial (Fin r) 𝕜), P ≠ 0 → ∀ {T : Set 𝕜}, T.Infinite →
      ∃ a : Fin r → 𝕜, Function.Injective a ∧ (∀ i, a i ∈ T) ∧ MvPolynomial.eval a P ≠ 0 :=
  fun {_r} P hP {_T} hT => exists_injective_eval_ne_zero_domain P hP hT

/-- **Distinct-multiset permanent symbols are complex-independent.**  For a family `S` of order tuples
of common total order, pairwise distinct as multisets, any nonzero complex combination of the cast
permanent symbols is a nonzero polynomial. -/
theorem combination_permSymbolPolyC_ne_zero {r : ℕ} {S : Finset (Fin r → ℕ)} {O : ℕ}
    (hO : ∀ μ ∈ S, ∑ t, μ t = O)
    (hdistinct : ∀ μ ∈ S, ∀ ν ∈ S, (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν)
    (c : (Fin r → ℕ) → ℂ) {μ₀ : Fin r → ℕ} (hμ₀ : μ₀ ∈ S) (hc : c μ₀ ≠ 0) :
    (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ)) ≠ 0 :=
  combination_permSymbolPolyMap_ne_zero (R := ℂ) hO hdistinct c hμ₀ hc

/-- **Ring-hom naturality of evaluation.**  A ring hom `h` commutes with multivariate evaluation and
the coefficient map: `h (eval g p) = eval (h ∘ g) (map h p)`. -/
theorem eval_map_ringHom {A B σ : Type*} [CommRing A] [CommRing B] (h : A →+* B) (g : σ → A)
    (p : MvPolynomial σ A) :
    h (MvPolynomial.eval g p) = MvPolynomial.eval (fun i => h (g i)) (MvPolynomial.map h p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- **Complex evaluation of the cast permanent symbol.**  Evaluating the `ℤ→ℂ` cast of
`permSymbolPoly μ` at integer scales `s` produces the complex falling-factorial permanent. -/
theorem eval_map_permSymbolPoly_complex {r : ℕ} (μ s : Fin r → ℕ) :
    MvPolynomial.eval (fun i => (s i : ℂ)) ((permSymbolPoly μ).map (Int.castRingHom ℂ))
      = ∑ π : Equiv.Perm (Fin r), ∏ t, (Nat.descFactorial (s (π t)) (μ t) : ℂ) := by
  have h := eval_map_ringHom (Int.castRingHom ℂ) (fun i => (s i : ℤ)) (permSymbolPoly μ)
  simp only [Int.coe_castRingHom, Int.cast_natCast] at h
  rw [← h, eval_permSymbolPoly]
  push_cast
  rfl

/-- **Complex coefficient identity.**  At the order-`O` distinct-scale index, the coefficient of a
complex-coefficient order-`O` degree-`r`-homogeneous differential polynomial factors as the product
of the source coefficients times the complex evaluation of the combined cast permanent symbol. -/
theorem coeff_combination_complex_eq {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ}
    (hb0 : 0 < bnat 0) (hstair : ∀ n, r * bnat n < bnat (n + 1)) (hbnatinj : Function.Injective bnat)
    {S : Finset (Fin r → ℕ)} {O : ℕ} (hO : ∀ μ ∈ S, ∑ t, μ t = O)
    (c : (Fin r → ℕ) → ℂ) {f : ℂ⟦X⟧}
    (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (M : Fin r → ℕ) (hMinj : Function.Injective M)
    (hbig : ∀ μ ∈ S, ∀ i t, μ t ≤ bnat (M i)) :
    coeff (∑ t, bnat (M t) - O) (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f)
      = (∏ i, coeff (bnat (M i)) f)
        * MvPolynomial.eval (fun i => (bnat (M i) : ℂ))
            (∑ μ ∈ S, MvPolynomial.C (c μ) * (permSymbolPoly μ).map (Int.castRingHom ℂ)) := by
  classical
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [map_smul, smul_eq_mul]
  have hidx : (∑ t, bnat (M t) - O) = ∑ t, (bnat (M t) - μ t) := by
    rw [Finset.sum_tsub_distrib Finset.univ (fun t _ => hbig μ hμ t t), hO μ hμ]
  rw [hidx, coeff_distinct_index_eq_permanent hmono hb0 hstair hbnatinj μ hsupp M hMinj
    (fun i t => hbig μ hμ i t), MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_map_permSymbolPoly_complex]
  ring

/-- **Coefficient of a degree-homogeneous differential polynomial at a distinct index.**  At the
distinct-scale index `∑ₜ bnat (M t) − O`, the coefficient of an order-`O` degree-`r`-homogeneous
differential polynomial `∑_{μ∈S} c_μ ∏ₜ f^{(μₜ)}` factors as `(∏ᵢ coeff (bnat Mᵢ) f)` times the
integer evaluation of the combined permanent symbol `∑_{μ∈S} C(c_μ) · permSymbolPoly μ`. -/
theorem coeff_combination_eq {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ}
    (hb0 : 0 < bnat 0) (hstair : ∀ n, r * bnat n < bnat (n + 1)) (hbnatinj : Function.Injective bnat)
    {S : Finset (Fin r → ℕ)} {O : ℕ} (hO : ∀ μ ∈ S, ∑ t, μ t = O)
    (c : (Fin r → ℕ) → ℤ) {f : ℂ⟦X⟧}
    (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (M : Fin r → ℕ) (hMinj : Function.Injective M)
    (hbig : ∀ μ ∈ S, ∀ i t, μ t ≤ bnat (M i)) :
    coeff (∑ t, bnat (M t) - O) (∑ μ ∈ S, (c μ : ℂ) • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f)
      = (∏ i, coeff (bnat (M i)) f)
        * (((MvPolynomial.eval (fun i => (bnat (M i) : ℤ)))
            (∑ μ ∈ S, MvPolynomial.C (c μ) * permSymbolPoly μ) : ℤ) : ℂ) := by
  have hmap : ((MvPolynomial.eval (fun i => (bnat (M i) : ℤ))
        (∑ μ ∈ S, MvPolynomial.C (c μ) * permSymbolPoly μ) : ℤ) : ℂ)
      = MvPolynomial.eval (fun i => (bnat (M i) : ℂ))
          (∑ μ ∈ S, MvPolynomial.C ((c μ : ℂ)) * (permSymbolPoly μ).map (Int.castRingHom ℂ)) := by
    have hpoly : MvPolynomial.map (Int.castRingHom ℂ)
          (∑ μ ∈ S, MvPolynomial.C (c μ) * permSymbolPoly μ)
        = ∑ μ ∈ S, MvPolynomial.C ((c μ : ℂ)) * (permSymbolPoly μ).map (Int.castRingHom ℂ) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [map_mul, MvPolynomial.map_C]
      simp
    have h := eval_map_ringHom (Int.castRingHom ℂ) (fun i => (bnat (M i) : ℤ))
      (∑ μ ∈ S, MvPolynomial.C (c μ) * permSymbolPoly μ)
    rw [hpoly] at h
    simp only [Int.coe_castRingHom, Int.cast_natCast] at h
    exact h
  rw [hmap]
  exact coeff_combination_complex_eq hmono hb0 hstair hbnatinj hO (fun μ => (c μ : ℂ)) hsupp M
    hMinj hbig

/-- **Complex degree-homogeneous survival.**  A nonzero complex-coefficient order-`O`
degree-`r`-homogeneous differential polynomial over a distinct-multiset family does not annihilate a
tail-supported superlacunary gap series. -/
theorem degHom_survives_complex {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ}
    (hb0 : 0 < bnat 0) (hstair : ∀ n, r * bnat n < bnat (n + 1)) (hbnatinj : Function.Injective bnat)
    (hbtop : Filter.Tendsto bnat Filter.atTop Filter.atTop)
    {S : Finset (Fin r → ℕ)} {O : ℕ} (hO : ∀ μ ∈ S, ∑ t, μ t = O)
    (hdistinct : ∀ μ ∈ S, ∀ ν ∈ S, (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν)
    (c : (Fin r → ℕ) → ℂ) {μ₀ : Fin r → ℕ} (hμ₀ : μ₀ ∈ S) (hc : c μ₀ ≠ 0)
    {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (hinf : {M : ℕ | coeff (bnat M) f ≠ 0}.Infinite) :
    (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) ≠ 0 := by
  classical
  intro hPzero
  have hΦne : (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ)) ≠ 0 :=
    combination_permSymbolPolyC_ne_zero hO hdistinct c hμ₀ hc
  set B := S.sup (fun μ => Finset.univ.sup μ) with hBdef
  have hB : ∀ μ ∈ S, ∀ t, μ t ≤ B :=
    fun μ hμ t => le_trans (Finset.le_sup (Finset.mem_univ t)) (Finset.le_sup hμ)
  obtain ⟨NB, hNB⟩ := Filter.eventually_atTop.mp (hbtop.eventually_ge_atTop B)
  set G := {n : ℕ | coeff (bnat n) f ≠ 0 ∧ NB ≤ n} with hGdef
  have hGinf : G.Infinite := by
    apply (hinf.diff (Set.finite_Iio NB)).mono
    intro n hn
    exact ⟨hn.1, not_lt.mp hn.2⟩
  have hTinf : ((fun n => (bnat n : ℂ)) '' G).Infinite :=
    hGinf.image (fun a _ b _ h => hbnatinj (by exact_mod_cast h))
  obtain ⟨a, hainj, haT, haΦ⟩ :=
    exists_injective_eval_ne_zero_field
      (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ)) hΦne hTinf
  choose M hMG hMeq using fun i => haT i
  have haM : a = fun i => ((bnat (M i) : ℂ)) := funext fun i => (hMeq i).symm
  have hMinj : Function.Injective M := by
    intro i j h
    apply hainj
    rw [← hMeq i, ← hMeq j, h]
  have hbig : ∀ μ ∈ S, ∀ i t, μ t ≤ bnat (M i) :=
    fun μ hμ i t => le_trans (hB μ hμ t) (hNB (M i) (hMG i).2)
  have hprodne : (∏ i, coeff (bnat (M i)) f) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (hMG i).1
  have hkey := coeff_combination_complex_eq hmono hb0 hstair hbnatinj hO c hsupp M hMinj hbig
  rw [hPzero, map_zero] at hkey
  have hevalne : MvPolynomial.eval (fun i => (bnat (M i) : ℂ))
      (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ)) ≠ 0 := by
    rw [← haM]; exact haΦ
  exact (mul_ne_zero hprodne hevalne) hkey.symm

/-- **Unconditional degree-homogeneous survival.**  A nonzero order-`O` degree-`r`-homogeneous
differential polynomial with integer coefficients, whose distinct order-multisets are the family
`S`, does not annihilate a tail-supported superlacunary gap series.  This supersedes the
leading-symbol nonvanishing hypothesis of `exists_threshold_degHom_diffPoly_gap_ne_zero`: the
distinct-index permanent symbol is always non-degenerate. -/
theorem degHom_survives {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ}
    (hb0 : 0 < bnat 0) (hstair : ∀ n, r * bnat n < bnat (n + 1)) (hbnatinj : Function.Injective bnat)
    (hbtop : Filter.Tendsto bnat Filter.atTop Filter.atTop)
    {S : Finset (Fin r → ℕ)} {O : ℕ} (hO : ∀ μ ∈ S, ∑ t, μ t = O)
    (hdistinct : ∀ μ ∈ S, ∀ ν ∈ S, (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν)
    (c : (Fin r → ℕ) → ℤ) {μ₀ : Fin r → ℕ} (hμ₀ : μ₀ ∈ S) (hc : c μ₀ ≠ 0)
    {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (hinf : {M : ℕ | coeff (bnat M) f ≠ 0}.Infinite) :
    (∑ μ ∈ S, (c μ : ℂ) • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) ≠ 0 :=
  degHom_survives_complex hmono hb0 hstair hbnatinj hbtop hO hdistinct (fun μ => (c μ : ℂ)) hμ₀
    (Int.cast_ne_zero.mpr hc) hsupp hinf

/-- **Wrong-order vanishing at a distinct index.**  With the window hypotheses, a differential
monomial of total order `O' ≠ O` (both `≤ W`) has zero coefficient at the order-`O` distinct-scale
index: any surviving source configuration would have `bnat`-mass off the target by `|O' − O| ≤ W`,
which the window uniqueness forbids. -/
theorem coeff_distinct_wrong_order_vanish {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1))
    {ν : Fin r → ℕ} {O' : ℕ} (hν : ∑ t, ν t = O')
    {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (M : Fin r → ℕ) (hMinj : Function.Injective M)
    {O : ℕ} (hOle : O ≤ ∑ t, bnat (M t)) (hOW : O ≤ W) (hO'W : O' ≤ W) (hOO' : O ≠ O') :
    coeff (∑ t, bnat (M t) - O) (∏ t, (⇑(d⁄dX ℂ))^[ν t] f) = 0 := by
  classical
  have hvanish : ∀ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag (∑ t, bnat (M t) - O),
      l ∉ (∅ : Finset (Fin r →₀ ℕ)) → ∃ t, coeff (l t + ν t) f = 0 := by
    intro l hl _
    by_contra hcon
    push Not at hcon
    choose n hn using fun t => hsupp (l t + ν t) (hcon t)
    have hsumN : ∑ t, l t = ∑ t, bnat (M t) - O := (Finset.mem_finsuppAntidiag.mp hl).1
    have hnmass : ∑ t, bnat (n t) = ∑ t, bnat (M t) - O + O' := by
      have e : ∑ t, bnat (n t) = ∑ t, (l t + ν t) := Finset.sum_congr rfl (fun t _ => (hn t).symm)
      rw [e, Finset.sum_add_distrib, hsumN, hν]
    have hmn : (Multiset.map bnat (Finset.univ.val.map n)).sum = ∑ t, bnat (n t) := by
      rw [Multiset.map_map]; rfl
    have hmM : (Multiset.map bnat (Finset.univ.val.map M)).sum = ∑ t, bnat (M t) := by
      rw [Multiset.map_map]; rfl
    obtain ⟨_, hmass⟩ := multiset_source_window_unique hmono hb0 hWb hW
      (s := Finset.univ.val.map n) (t := Finset.univ.val.map M) (by simp) (by simp)
      (Finset.univ.nodup.map hMinj)
      (by rw [hmn, hmM]; omega) (by rw [hmn, hmM]; omega)
    rw [hmn, hmM, hnmass] at hmass
    exact hOO' (by omega)
  rw [coeff_prod_iterate_derivative_of_subset ν f (∑ t, bnat (M t) - O) ∅
    (Finset.empty_subset _) hvanish, Finset.sum_empty]

/-- **Wrong-degree vanishing at a distinct index.**  A differential monomial of total degree
`D' ≠ D` has zero coefficient at the degree-`D` distinct-scale index: a surviving source
configuration would have `D'` sources with `bnat`-mass within `W` of the `D` target scales, forcing
(card-free window uniqueness) the source and target multisets to coincide — impossible when
`D' ≠ D`. -/
theorem coeff_distinct_wrong_degree_vanish {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1))
    {D D' : ℕ} (hDr : D ≤ r) (hD'r : D' ≤ r) (hDD' : D ≠ D')
    {ν : Fin D' → ℕ} {O' : ℕ} (hν : ∑ t, ν t = O') (hO'W : O' ≤ W)
    {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (M : Fin D → ℕ) (hMinj : Function.Injective M)
    {O : ℕ} (hOle : O ≤ ∑ i, bnat (M i)) (hOW : O ≤ W) :
    coeff (∑ i, bnat (M i) - O) (∏ t, (⇑(d⁄dX ℂ))^[ν t] f) = 0 := by
  classical
  have hvanish : ∀ l ∈ (Finset.univ : Finset (Fin D')).finsuppAntidiag (∑ i, bnat (M i) - O),
      l ∉ (∅ : Finset (Fin D' →₀ ℕ)) → ∃ t, coeff (l t + ν t) f = 0 := by
    intro l hl _
    by_contra hcon
    push Not at hcon
    choose n hn using fun t => hsupp (l t + ν t) (hcon t)
    have hsumN : ∑ t, l t = ∑ i, bnat (M i) - O := (Finset.mem_finsuppAntidiag.mp hl).1
    have hnmass : ∑ t, bnat (n t) = ∑ i, bnat (M i) - O + O' := by
      have e : ∑ t, bnat (n t) = ∑ t, (l t + ν t) := Finset.sum_congr rfl (fun t _ => (hn t).symm)
      rw [e, Finset.sum_add_distrib, hsumN, hν]
    have hmn : (Multiset.map bnat (Finset.univ.val.map n)).sum = ∑ t, bnat (n t) := by
      rw [Multiset.map_map]; rfl
    have hmM : (Multiset.map bnat (Finset.univ.val.map M)).sum = ∑ i, bnat (M i) := by
      rw [Multiset.map_map]; rfl
    have hcardn : (Finset.univ.val.map n : Multiset ℕ).card = D' := by simp
    have hcardM : (Finset.univ.val.map M : Multiset ℕ).card = D := by simp
    have hseq := multiset_source_window_free hmono hb0 hWb hW
      (s := Finset.univ.val.map n) (t := Finset.univ.val.map M)
      (by rw [hcardn]; exact hD'r) (by rw [hcardM]; exact hDr)
      (Finset.univ.nodup.map hMinj)
      (by rw [hmn, hmM]; omega) (by rw [hmn, hmM]; omega)
    have hcardeq : D' = D := by
      have := congrArg Multiset.card hseq; rw [hcardn, hcardM] at this; exact this
    exact hDD' hcardeq.symm
  rw [coeff_prod_iterate_derivative_of_subset ν f (∑ i, bnat (M i) - O) ∅
    (Finset.empty_subset _) hvanish, Finset.sum_empty]

/-- **Two-sided window vanishing.**  At an arbitrary index `K`, a differential monomial of degree
`D'` vanishes whenever its required source mass `K + ∑ν` lies within the window `W` of the target
mass `∑bnat Mᵢ` but does not equal it — any surviving source configuration would (card-free window
uniqueness) coincide with the target multiset, forcing exact mass.  This subsumes both the wrong-order
and wrong-degree vanishing and handles the integer offset `δ = m₀ − O` of the z-shifted probe with a
single hypothesis, regardless of sign. -/
theorem coeff_distinct_vanish_window {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1))
    {D D' : ℕ} (hDr : D ≤ r) (hD'r : D' ≤ r)
    {ν : Fin D' → ℕ} {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (M : Fin D → ℕ) (hMinj : Function.Injective M) {K : ℕ}
    (hne : K + ∑ t, ν t ≠ ∑ i, bnat (M i))
    (hle1 : K + ∑ t, ν t ≤ (∑ i, bnat (M i)) + W)
    (hle2 : (∑ i, bnat (M i)) ≤ K + ∑ t, ν t + W) :
    coeff K (∏ t, (⇑(d⁄dX ℂ))^[ν t] f) = 0 := by
  classical
  have hvanish : ∀ l ∈ (Finset.univ : Finset (Fin D')).finsuppAntidiag K,
      l ∉ (∅ : Finset (Fin D' →₀ ℕ)) → ∃ t, coeff (l t + ν t) f = 0 := by
    intro l hl _
    by_contra hcon
    push Not at hcon
    choose n hn using fun t => hsupp (l t + ν t) (hcon t)
    have hsumK : ∑ t, l t = K := (Finset.mem_finsuppAntidiag.mp hl).1
    have hnmass : ∑ t, bnat (n t) = K + ∑ t, ν t := by
      have e : ∑ t, bnat (n t) = ∑ t, (l t + ν t) := Finset.sum_congr rfl (fun t _ => (hn t).symm)
      rw [e, Finset.sum_add_distrib, hsumK]
    have hmn : (Multiset.map bnat (Finset.univ.val.map n)).sum = ∑ t, bnat (n t) := by
      rw [Multiset.map_map]; rfl
    have hmM : (Multiset.map bnat (Finset.univ.val.map M)).sum = ∑ i, bnat (M i) := by
      rw [Multiset.map_map]; rfl
    have hseq := multiset_source_window_free hmono hb0 hWb hW
      (s := Finset.univ.val.map n) (t := Finset.univ.val.map M)
      (by simpa using hD'r) (by simpa using hDr) (Finset.univ.nodup.map hMinj)
      (by rw [hmn, hmM]; omega) (by rw [hmn, hmM]; omega)
    apply hne
    have hmasseq : (Multiset.map bnat (Finset.univ.val.map n)).sum
        = (Multiset.map bnat (Finset.univ.val.map M)).sum := by rw [hseq]
    rw [hmn, hmM, hnmass] at hmasseq
    exact hmasseq
  rw [coeff_prod_iterate_derivative_of_subset ν f K ∅ (Finset.empty_subset _) hvanish,
    Finset.sum_empty]

/-- **Complex order-`O` reduction.**  At the order-`O` distinct index, the coefficient of a
complex-coefficient mixed-order differential polynomial equals that of its order-`O` subfamily. -/
theorem coeff_mixed_eq_orderO_complex {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ} {W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1))
    {S : Finset (Fin r → ℕ)} (hbound : ∀ ν ∈ S, ∑ t, ν t ≤ W)
    (c : (Fin r → ℕ) → ℂ) {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (M : Fin r → ℕ) (hMinj : Function.Injective M)
    {O : ℕ} (hOle : O ≤ ∑ t, bnat (M t)) (hOW : O ≤ W) :
    coeff (∑ t, bnat (M t) - O) (∑ ν ∈ S, c ν • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f)
      = coeff (∑ t, bnat (M t) - O)
          (∑ ν ∈ S.filter (fun ν => ∑ t, ν t = O), c ν • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f) := by
  classical
  rw [map_sum, map_sum, ← Finset.sum_filter_add_sum_filter_not S (fun ν => ∑ t, ν t = O)]
  have hrest : ∑ ν ∈ S.filter (fun ν => ¬ ∑ t, ν t = O),
      coeff (∑ t, bnat (M t) - O) (c ν • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f) = 0 := by
    apply Finset.sum_eq_zero
    intro ν hν
    rw [Finset.mem_filter] at hν
    rw [map_smul,
      coeff_distinct_wrong_order_vanish hmono hb0 hWb hW rfl hsupp M hMinj hOle hOW
        (hbound ν hν.1) (fun h => hν.2 h.symm), smul_zero]
  rw [hrest, add_zero]

/-- **Order-`O` reduction of the coefficient.**  At the order-`O` distinct index, the coefficient of
a mixed-order differential polynomial equals that of its order-`O` subfamily — every other-order
monomial contributes zero. -/
theorem coeff_mixed_eq_orderO {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1))
    {S : Finset (Fin r → ℕ)} (hbound : ∀ ν ∈ S, ∑ t, ν t ≤ W)
    (c : (Fin r → ℕ) → ℤ) {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (M : Fin r → ℕ) (hMinj : Function.Injective M)
    {O : ℕ} (hOle : O ≤ ∑ t, bnat (M t)) (hOW : O ≤ W) :
    coeff (∑ t, bnat (M t) - O) (∑ ν ∈ S, (c ν : ℂ) • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f)
      = coeff (∑ t, bnat (M t) - O)
          (∑ ν ∈ S.filter (fun ν => ∑ t, ν t = O), (c ν : ℂ) • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f) :=
  coeff_mixed_eq_orderO_complex hmono hb0 hWb hW hbound (fun ν => (c ν : ℂ)) hsupp M hMinj hOle
    hOW

/-- **Complex fixed-degree survival.**  A nonzero complex-coefficient degree-`r`-homogeneous
differential polynomial with arbitrary bounded orders over a distinct-multiset family does not
annihilate a tail-supported superlacunary gap series. -/
theorem diffPoly_fixedDegree_survives_complex {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r : ℕ} {W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1))
    (hbnatinj : Function.Injective bnat) (hbtop : Filter.Tendsto bnat Filter.atTop Filter.atTop)
    {S : Finset (Fin r → ℕ)} (hbound : ∀ ν ∈ S, ∑ t, ν t ≤ W)
    (hdistinct : ∀ μ ∈ S, ∀ ν ∈ S, (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν)
    (c : (Fin r → ℕ) → ℂ) {μ₀ : Fin r → ℕ} (hμ₀ : μ₀ ∈ S) (hc : c μ₀ ≠ 0)
    {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (hinf : {M : ℕ | coeff (bnat M) f ≠ 0}.Infinite) :
    (∑ ν ∈ S, c ν • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f) ≠ 0 := by
  classical
  intro hPzero
  set O := ∑ t, μ₀ t with hOdef
  set SO := S.filter (fun ν => ∑ t, ν t = O) with hSOdef
  have hμ₀O : μ₀ ∈ SO := Finset.mem_filter.mpr ⟨hμ₀, rfl⟩
  have hOall : ∀ ν ∈ SO, ∑ t, ν t = O := fun ν hν => (Finset.mem_filter.mp hν).2
  have hdistinctSO : ∀ μ ∈ SO, ∀ ν ∈ SO,
      (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν :=
    fun μ hμ ν hν => hdistinct μ (Finset.mem_filter.mp hμ).1 ν (Finset.mem_filter.mp hν).1
  have hstair : ∀ n, r * bnat n < bnat (n + 1) := fun n => lt_of_le_of_lt (Nat.le_add_right _ _) (hW n)
  obtain ⟨NB, hNB⟩ := Filter.eventually_atTop.mp (hbtop.eventually_ge_atTop W)
  set G := {n : ℕ | coeff (bnat n) f ≠ 0 ∧ NB ≤ n} with hGdef
  have hGinf : G.Infinite := by
    apply (hinf.diff (Set.finite_Iio NB)).mono
    intro n hn; exact ⟨hn.1, not_lt.mp hn.2⟩
  have hTinf : ((fun n => (bnat n : ℂ)) '' G).Infinite :=
    hGinf.image (fun a _ b _ h => hbnatinj (by exact_mod_cast h))
  obtain ⟨a, hainj, haT, haΦ⟩ :=
    exists_injective_eval_ne_zero_field
      (∑ ν ∈ SO, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ))
      (combination_permSymbolPolyC_ne_zero hOall hdistinctSO c hμ₀O hc) hTinf
  choose M hMG hMeq using fun i => haT i
  have haM : a = fun i => ((bnat (M i) : ℂ)) := funext fun i => (hMeq i).symm
  have hMinj : Function.Injective M := fun i j h => hainj (by rw [← hMeq i, ← hMeq j, h])
  have hbig : ∀ ν ∈ SO, ∀ i t, ν t ≤ bnat (M i) := by
    intro ν hν i t
    calc ν t ≤ ∑ t, ν t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      _ = O := hOall ν hν
      _ ≤ W := hOdef.symm ▸ hbound μ₀ hμ₀
      _ ≤ bnat (M i) := hNB (M i) (hMG i).2
  have hprodne : (∏ i, coeff (bnat (M i)) f) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (hMG i).1
  have hOW : O ≤ W := hOdef.symm ▸ hbound μ₀ hμ₀
  have hOle : O ≤ ∑ t, bnat (M t) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    · subst hr0; simp [hOdef]
    · obtain ⟨t0⟩ : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr1
      calc O ≤ bnat (M t0) := le_trans hOW (hNB (M t0) (hMG t0).2)
        _ ≤ ∑ t, bnat (M t) :=
            Finset.single_le_sum (f := fun t => bnat (M t)) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ t0)
  have hkey1 := coeff_mixed_eq_orderO_complex hmono hb0 hWb hW hbound c hsupp M hMinj hOle hOW
  have hkey2 := coeff_combination_complex_eq hmono hb0 hstair hbnatinj hOall c hsupp M hMinj hbig
  rw [hPzero, map_zero, hkey2] at hkey1
  have hevalne : MvPolynomial.eval (fun i => (bnat (M i) : ℂ))
      (∑ ν ∈ SO, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ)) ≠ 0 := by
    rw [← haM]; exact haΦ
  exact (mul_ne_zero hprodne hevalne) hkey1.symm

/-- **Fixed-degree survival, arbitrary orders.**  A nonzero degree-`r`-homogeneous differential
polynomial with integer coefficients over a distinct-multiset family `S` of bounded order does not
annihilate a tail-supported superlacunary gap series.  Reduces to `degHom_survives` on the order
class of `μ₀`: the other-order monomials vanish at that class's distinct index. -/
theorem diffPoly_fixedDegree_survives {bnat : ℕ → ℕ} (hmono : Monotone bnat) {r W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1))
    (hbnatinj : Function.Injective bnat) (hbtop : Filter.Tendsto bnat Filter.atTop Filter.atTop)
    {S : Finset (Fin r → ℕ)} (hbound : ∀ ν ∈ S, ∑ t, ν t ≤ W)
    (hdistinct : ∀ μ ∈ S, ∀ ν ∈ S, (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν)
    (c : (Fin r → ℕ) → ℤ) {μ₀ : Fin r → ℕ} (hμ₀ : μ₀ ∈ S) (hc : c μ₀ ≠ 0)
    {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (hinf : {M : ℕ | coeff (bnat M) f ≠ 0}.Infinite) :
    (∑ ν ∈ S, (c ν : ℂ) • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f) ≠ 0 :=
  diffPoly_fixedDegree_survives_complex hmono hb0 hWb hW hbnatinj hbtop hbound hdistinct
    (fun ν => (c ν : ℂ)) hμ₀ (Int.cast_ne_zero.mpr hc) hsupp hinf

end GaloisForLFunctions
