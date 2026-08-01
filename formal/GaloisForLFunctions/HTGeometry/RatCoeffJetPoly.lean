import GaloisForLFunctions.HTGeometry.JetPolyLineDatum
import GaloisForLFunctions.HTGeometry.FullJetPolyNonzeroDatum
import GaloisForLFunctions.HTGeometry.SupportReindex

/-!
# Jet polynomials with rational coefficients

The datum of a jet polynomial does not need constant coefficients.  A coefficient `p(s)/s^d` is the
germ of a rational function, so the whole expression is again a value of the digamma jet evaluation
map, and the same two ingredients — Hölder's theorem on the half-plane and the rigidity of standard
rational approximations across lines — give its datum from nonvanishing alone.
-/

open Filter Topology Complex MvPolynomial Finset

namespace GaloisForLFunctions

/-- **The germ of a coefficient.**  The rational function `p/X^d` has the germ of `p(s)/s^d`. -/
theorem ratGerm_div_polyPow (σ₀ : ℝ) (p : Polynomial ℂ) (d : ℕ) :
    ratGerm σ₀ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p / (RatFunc.X : RatFunc ℂ) ^ d)
      = ((fun s : ℂ => p.eval s / s ^ d : ℂ → ℂ) : HalfPlaneGerm σ₀) := by
  have hXpoly : ((Polynomial.X : Polynomial ℂ) ^ d) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hXrat : ((RatFunc.X : RatFunc ℂ) ^ d) ≠ 0 := pow_ne_zero _ ratFuncX_ne_zero
  have hunit : IsUnit (polyGerm σ₀ ((Polynomial.X : Polynomial ℂ) ^ d)) :=
    isUnit_polyGerm σ₀ hXpoly
  refine hunit.mul_left_cancel ?_
  have hrat : algebraMap (Polynomial ℂ) (RatFunc ℂ) ((Polynomial.X : Polynomial ℂ) ^ d)
      * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p / (RatFunc.X : RatFunc ℂ) ^ d)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) p := by
    rw [map_pow, RatFunc.algebraMap_X, mul_comm, div_mul_cancel₀ _ hXrat]
  have hleft : polyGerm σ₀ ((Polynomial.X : Polynomial ℂ) ^ d)
      * ratGerm σ₀ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p / (RatFunc.X : RatFunc ℂ) ^ d)
      = polyGerm σ₀ p := by
    rw [← ratGerm_algebraMap σ₀ ((Polynomial.X : Polynomial ℂ) ^ d), ← map_mul, hrat,
      ratGerm_algebraMap]
  rw [hleft, polyGerm_apply, polyGerm_apply, ← Filter.Germ.coe_mul]
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [eventually_ne_zero σ₀] with s hs
  have hpow : (s : ℂ) ^ d ≠ 0 := pow_ne_zero _ hs
  show p.eval s = Polynomial.eval s ((Polynomial.X : Polynomial ℂ) ^ d) * (p.eval s / s ^ d)
  rw [Polynomial.eval_pow, Polynomial.eval_X]
  field_simp

/-- A jet polynomial with coefficients `p(s)/s^d`, as a polynomial in the jet variables. -/
noncomputable def jetPolyMvCoeff (N M d : ℕ) (a : Fin M → Polynomial ℂ)
    (e : Fin M → Fin N → ℕ) : MvPolynomial (Fin (N + 1)) (RatFunc ℂ) :=
  ∑ α : Fin M, MvPolynomial.C
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (a α) / (RatFunc.X : RatFunc ℂ) ^ d)
    * ∏ i : Fin N, (MvPolynomial.X i.succ) ^ e α i

/-- **A jet polynomial with a nonzero coefficient is nonzero.** -/
theorem jetPolyMvCoeff_ne_zero {N M d : ℕ} (a : Fin M → Polynomial ℂ) (e : Fin M → Fin N → ℕ)
    (he : Function.Injective e) {β : Fin M} (hβ : a β ≠ 0) : jetPolyMvCoeff N M d a e ≠ 0 := by
  classical
  intro h0
  have hcoeff : MvPolynomial.coeff (jetExp (e β)) (jetPolyMvCoeff N M d a e)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (a β) / (RatFunc.X : RatFunc ℂ) ^ d := by
    rw [jetPolyMvCoeff, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single β]
    · rw [prod_X_succ_pow, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, if_pos rfl,
        mul_one]
    · intro α _ hαβ
      rw [prod_X_succ_pow, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
        if_neg (fun h => hαβ (he (jetExp_injective h))), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ β) h
  rw [h0, MvPolynomial.coeff_zero] at hcoeff
  have hXrat : ((RatFunc.X : RatFunc ℂ) ^ d) ≠ 0 := pow_ne_zero _ ratFuncX_ne_zero
  have hnum : algebraMap (Polynomial ℂ) (RatFunc ℂ) (a β) = 0 := by
    have := hcoeff.symm
    rwa [div_eq_zero_iff, or_iff_left hXrat] at this
  exact hβ (RatFunc.algebraMap_injective ℂ (by rw [hnum, map_zero]))

/-- The evaluation at the digamma jets is the germ of the function on the line. -/
theorem digammaJetEval_jetPolyMvCoeff (σ₀ : ℝ) (N M d : ℕ) (a : Fin M → Polynomial ℂ)
    (e : Fin M → Fin N → ℕ) :
    digammaJetEval σ₀ (N + 1) (jetPolyMvCoeff N M d a e)
      = ((fun s : ℂ => ∑ α : Fin M, ((a α).eval s / s ^ d) * ∏ i : Fin N,
          iteratedDeriv ((i : ℕ) + 1) Complex.digamma s ^ e α i : ℂ → ℂ) : HalfPlaneGerm σ₀) := by
  classical
  set Φ : (ℂ → ℂ) →+* HalfPlaneGerm σ₀ := Filter.Germ.coeRingHom (halfPlaneUpper σ₀) with hΦ
  have hgoal : ((fun s : ℂ => ∑ α : Fin M, ((a α).eval s / s ^ d) * ∏ i : Fin N,
      iteratedDeriv ((i : ℕ) + 1) Complex.digamma s ^ e α i : ℂ → ℂ) : HalfPlaneGerm σ₀)
      = ∑ α : Fin M, Φ (fun s : ℂ => (a α).eval s / s ^ d)
          * ∏ i : Fin N, Φ (fun s : ℂ => iteratedDeriv ((i : ℕ) + 1) Complex.digamma s) ^ e α i := by
    have hpush : ∑ α : Fin M, Φ (fun s : ℂ => (a α).eval s / s ^ d)
        * ∏ i : Fin N, Φ (fun s : ℂ => iteratedDeriv ((i : ℕ) + 1) Complex.digamma s) ^ e α i
        = Φ (∑ α : Fin M, (fun s : ℂ => (a α).eval s / s ^ d)
            * ∏ i : Fin N, (fun s : ℂ => iteratedDeriv ((i : ℕ) + 1) Complex.digamma s) ^ e α i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_mul, map_prod]
      simp only [map_pow]
    rw [hpush]
    congr 1
    funext s
    simp [Finset.sum_apply, Finset.prod_apply]
  rw [hgoal, jetPolyMvCoeff, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, map_prod]
  congr 1
  · rw [digammaJetEval_C, ratGerm_div_polyPow]
    rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, digammaJetEval_X, digammaJetGerm, Fin.val_succ]
    rfl

/-- **A nonzero jet polynomial with rational coefficients has bounded decay order on every line.** -/
theorem exists_not_isLineBigO_jetPolyCoeff {σ : ℝ} (hσ : 0 < σ) (N M W d : ℕ)
    (a : Fin M → Polynomial ℂ) (e : Fin M → Fin N → ℕ) (hdeg : ∀ α : Fin M, (a α).natDegree ≤ d)
    (hW : ∀ α : Fin M, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i)
    (hne : jetPolyMvCoeff N M d a e ≠ 0) :
    ∃ n : ℕ, ¬ IsLineBigO σ n (fun t : ℝ => ∑ α : Fin M,
      ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i) := by
  refine exists_not_isLineBigO_of_germ (W := W) hσ hne
    (digammaJetEval_jetPolyMvCoeff σ N M d a e) fun K => ?_
  obtain ⟨F, A, hstd, hA, hb⟩ := exists_jetPolyCoeff_package N M K W d e a hdeg hW
  exact ⟨F, A, hstd, le_trans zero_le_one hA, hb⟩

/-- **The datum of a nonzero jet polynomial with rational coefficients.** -/
theorem exists_jetPolyCoeff_datum_of_ne_zero {σ : ℝ} (hσ : 0 < σ) (N M W d : ℕ)
    (a : Fin M → Polynomial ℂ) (e : Fin M → Fin N → ℕ) (hdeg : ∀ α : Fin M, (a α).natDegree ≤ d)
    (hW : ∀ α : Fin M, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i)
    (hne : jetPolyMvCoeff N M d a e ≠ 0) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ Tendsto (fun t : ℝ =>
      ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * ∑ α : Fin M,
        ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i) atTop (nhds c) := by
  obtain ⟨n, hn⟩ := exists_not_isLineBigO_jetPolyCoeff hσ N M W d a e hdeg hW hne
  exact exists_jetPolyCoeff_datum hσ N M W d e a hdeg hW (n := n) hn

/-- **The datum of a nonzero jet polynomial with rational coefficients, over all orders.** -/
theorem exists_full_jetPolyCoeff_datum {σ : ℝ} (hσ : 0 < σ) {M K d : ℕ} (hM : 0 < M)
    (a : Fin M → Polynomial ℂ) (hdeg : ∀ α : Fin M, (a α).natDegree ≤ d)
    (E : Fin M → Fin (K + 1) → ℕ) (ha : ∀ α, a α ≠ 0) (hE : Function.Injective E) :
    ∃ (A B' : ℕ) (r : ℂ), r ≠ 0 ∧ Tendsto (fun t : ℝ =>
      (∑ α : Fin M, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d) * ∏ j : Fin (K + 1),
        iteratedDeriv (j : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α j)
        / polyJetShape σ A 0 B' t) atTop (nhds r) := by
  classical
  -- the positive-order part of a monomial
  let g : Fin M → ℝ → ℂ := fun α t => ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d) * ∏ i : Fin K,
    iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α i.succ
  let lg : Fin M → ℕ := fun α => E α 0
  let T : Finset ℕ := Finset.image lg Finset.univ
  have hTne : T.Nonempty := ⟨lg ⟨0, hM⟩, Finset.mem_image_of_mem lg (Finset.mem_univ _)⟩
  have hN : 0 < T.card := Finset.card_pos.mpr hTne
  let v : Fin T.card → ℕ := fun β => ((T.equivFin.symm β : {x // x ∈ T}) : ℕ)
  have hvinj : Function.Injective v := fun β γ hβγ =>
    T.equivFin.symm.injective (Subtype.ext hβγ)
  have hvmem : ∀ β, v β ∈ T := fun β => (T.equivFin.symm β).2
  -- each fibre of the logarithmic degree, reindexed by a `Fin`
  have hfib : ∀ β : Fin T.card, ∃ (M' : ℕ) (ι : Fin M' → Fin M), Function.Injective ι
      ∧ (∀ j, lg (ι j) = v β) ∧ (∀ α, lg α = v β → ∃ j, ι j = α)
      ∧ ∑ α ∈ Finset.univ.filter (fun α => lg α = v β), g α = ∑ j : Fin M', g (ι j) := by
    intro β
    obtain ⟨M', ι, hinj, hmem, hsurj, hsum⟩ :=
      exists_fin_reindex_of_finset (A := ℝ → ℂ) (Finset.univ.filter (fun α => lg α = v β)) g
    exact ⟨M', ι, hinj, fun j => (Finset.mem_filter.mp (hmem j)).2,
      fun α hα => hsurj α (Finset.mem_filter.mpr ⟨Finset.mem_univ α, hα⟩), hsum⟩
  choose M' ι hinj hfibmem hfibsurj hfibsum using hfib
  -- every fibre is nonempty, so its index type is
  have hM' : ∀ β, 0 < M' β := by
    intro β
    obtain ⟨α, -, hα⟩ := Finset.mem_image.mp (hvmem β)
    obtain ⟨j, -⟩ := hfibsurj β α hα
    exact Fin.pos j
  -- the exponents inside a fibre are distinct
  have hEfib : ∀ β, Function.Injective (fun j : Fin (M' β) => fun i : Fin K => E (ι β j) i.succ) := by
    intro β j k hjk
    refine hinj β ?_
    refine hE ?_
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [show E (ι β j) 0 = lg (ι β j) from rfl, show E (ι β k) 0 = lg (ι β k) from rfl,
        hfibmem β j, hfibmem β k]
    · exact congrFun hjk i
  -- each fibre sum is a nonzero jet polynomial, hence has a datum
  have hdat : ∀ β : Fin T.card, ∃ (p : ℕ) (r : ℂ), r ≠ 0 ∧
      Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * (∑ j : Fin (M' β), g (ι β j) t))
        atTop (nhds r) := by
    intro β
    have hne : jetPolyMvCoeff K (M' β) d (fun j => a (ι β j))
        (fun j i => E (ι β j) i.succ) ≠ 0 :=
      jetPolyMvCoeff_ne_zero _ _ (hEfib β) (β := ⟨0, hM' β⟩) (ha _)
    obtain ⟨p, r, hr, hlim⟩ :=
      exists_jetPolyCoeff_datum_of_ne_zero hσ K (M' β) 0 d (fun j => a (ι β j))
        (fun j i => E (ι β j) i.succ) (fun j => hdeg _) (fun _ => Nat.zero_le _) hne
    exact ⟨p, r, hr, hlim⟩
  choose p r hr hdatlim using hdat
  -- the polynomial is the sum of its groups, weighted by powers of `psi`
  have hsplit : ∀ t : ℝ, (∑ α : Fin M, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d) * ∏ j : Fin (K + 1),
      iteratedDeriv (j : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α j)
      = ∑ β : Fin T.card, Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ v β
          * (∑ j : Fin (M' β), g (ι β j) t) := by
    intro t
    have hmonomial : ∀ α : Fin M, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d) * ∏ j : Fin (K + 1),
        iteratedDeriv (j : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α j
        = Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ lg α * g α t := by
      intro α
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, iteratedDeriv_zero]
      ring
    rw [Finset.sum_congr rfl fun α _ => hmonomial α]
    have hmaps : ∀ α ∈ (Finset.univ : Finset (Fin M)),
        T.equivFin ⟨lg α, Finset.mem_image_of_mem lg (Finset.mem_univ α)⟩ ∈
          (Finset.univ : Finset (Fin T.card)) := fun α _ => Finset.mem_univ _
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun α => Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ lg α * g α t)]
    refine Finset.sum_congr rfl fun β _ => ?_
    have hfilter : (Finset.univ.filter fun α =>
          T.equivFin ⟨lg α, Finset.mem_image_of_mem lg (Finset.mem_univ α)⟩ = β)
        = Finset.univ.filter (fun α => lg α = v β) := by
      refine Finset.filter_congr fun α _ => ?_
      constructor
      · intro h
        have hsym : T.equivFin.symm β = ⟨lg α, Finset.mem_image_of_mem lg (Finset.mem_univ α)⟩ :=
          (Equiv.symm_apply_eq T.equivFin).mpr h.symm
        exact (congrArg (fun x : {x // x ∈ T} => (x : ℕ)) hsym).symm
      · intro h
        refine T.equivFin.symm.injective ?_
        rw [Equiv.symm_apply_apply]
        exact Subtype.ext (by simpa [v] using h)
    rw [hfilter]
    have hpull : ∑ α ∈ Finset.univ.filter (fun α => lg α = v β),
        Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ lg α * g α t
        = Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ v β
          * ∑ α ∈ Finset.univ.filter (fun α => lg α = v β), g α t := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [(Finset.mem_filter.mp hα).2]
    rw [hpull]
    congr 1
    have hev := congrFun (hfibsum β) t
    simpa [Finset.sum_apply] using hev
  obtain ⟨γ, hγ⟩ := exists_grouped_jetPoly_datum hσ hN
    (fun β t => ∑ j : Fin (M' β), g (ι β j) t) v hvinj p r hdatlim
  refine ⟨v γ, p γ, r γ, hr γ, ?_⟩
  refine hγ.congr fun t => ?_
  rw [hsplit t]

end GaloisForLFunctions
