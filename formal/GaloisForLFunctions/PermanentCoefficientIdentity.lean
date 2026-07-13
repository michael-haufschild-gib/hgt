import GaloisForLFunctions.DifferentialMonomialCoefficient
import GaloisForLFunctions.SuperIncreasingSourceUnique
import GaloisForLFunctions.PermanentDistinctSymbol
import GaloisForLFunctions.MvPolynomialInfiniteEval
import GaloisForLFunctions.IterateDerivativeFalling

/-!
# The distinct-index coefficient is a permanent

At `r` distinct source scales `bnat Mᵢ` the coefficient of a differential monomial `∏ₜ f^{(μₜ)}`
of a tail-supported superlacunary series is a **permanent** over those scales.  Unlike the balanced
index (all sources equal, a single surviving antidiagonal point → the weight polynomial), the
distinct index has `r!` surviving antidiagonal points — one per assignment `π` of the `r` factors to
the `r` scales — and they sum to `(∏ᵢ coeff (bnat Mᵢ) f) · permSymbol`.

The `coeff_prod_iterate_derivative_of_subset` lemma isolates the surviving set; `multiset_source_unique`
identifies it as exactly the permutation orbit of the balanced assignment.
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
  classical
  rw [map_sum, map_sum, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [map_smul, smul_eq_mul]
  have hidx : (∑ t, bnat (M t) - O) = ∑ t, (bnat (M t) - μ t) := by
    rw [Finset.sum_tsub_distrib Finset.univ (fun t _ => hbig μ hμ t t), hO μ hμ]
  rw [hidx, coeff_distinct_index_eq_permanent hmono hb0 hstair hbnatinj μ hsupp M hMinj
    (fun i t => hbig μ hμ i t), MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_permSymbolPoly]
  push_cast
  ring

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
    (∑ μ ∈ S, (c μ : ℂ) • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) ≠ 0 := by
  classical
  intro hPzero
  have hΦne : (∑ μ ∈ S, MvPolynomial.C (c μ) * permSymbolPoly μ) ≠ 0 :=
    combination_permSymbolPoly_ne_zero hO hdistinct c hμ₀ hc
  -- an order bound over the finite family `S`
  set B := S.sup (fun μ => Finset.univ.sup μ) with hBdef
  have hB : ∀ μ ∈ S, ∀ t, μ t ≤ B :=
    fun μ hμ t => le_trans (Finset.le_sup (Finset.mem_univ t)) (Finset.le_sup hμ)
  -- a scale threshold: `bnat n ≥ B` past some index
  obtain ⟨NB, hNB⟩ := Filter.eventually_atTop.mp (hbtop.eventually_ge_atTop B)
  -- the infinite set of admissible integer scales
  set G := {n : ℕ | coeff (bnat n) f ≠ 0 ∧ NB ≤ n} with hGdef
  have hGinf : G.Infinite := by
    apply (hinf.diff (Set.finite_Iio NB)).mono
    intro n hn
    exact ⟨hn.1, not_lt.mp hn.2⟩
  have hTinf : ((fun n => (bnat n : ℤ)) '' G).Infinite :=
    hGinf.image (fun a _ b _ h => hbnatinj (by exact_mod_cast h))
  obtain ⟨a, hainj, haT, haΦ⟩ :=
    exists_injective_eval_ne_zero (∑ μ ∈ S, MvPolynomial.C (c μ) * permSymbolPoly μ) hΦne hTinf
  choose M hMG hMeq using fun i => haT i
  -- `a = bnat ∘ M`
  have haM : a = fun i => ((bnat (M i) : ℤ)) := funext fun i => (hMeq i).symm
  have hMinj : Function.Injective M := by
    intro i j h
    apply hainj
    rw [← hMeq i, ← hMeq j, h]
  have hbig : ∀ μ ∈ S, ∀ i t, μ t ≤ bnat (M i) :=
    fun μ hμ i t => le_trans (hB μ hμ t) (hNB (M i) (hMG i).2)
  have hprodne : (∏ i, coeff (bnat (M i)) f) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (hMG i).1
  have hkey := coeff_combination_eq hmono hb0 hstair hbnatinj hO c hsupp M hMinj hbig
  rw [hPzero, map_zero] at hkey
  have hevalne : ((MvPolynomial.eval (fun i => (bnat (M i) : ℤ)))
      (∑ μ ∈ S, MvPolynomial.C (c μ) * permSymbolPoly μ) : ℤ) ≠ 0 := by
    rw [← haM]; exact haΦ
  exact (mul_ne_zero hprodne (Int.cast_ne_zero.mpr hevalne)) hkey.symm

end GaloisForLFunctions
