import GaloisForLFunctions.HTGeometry.LeeYangAsanoContraction
import GaloisForLFunctions.RHTower.LeeYangDatumFirstZero
import GaloisForLFunctions.RHTower.LeeYangProducerFieldDensity
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer

/-!
# Every ferromagnetic Ising graph is a Lee–Yang datum

The corpus's Lee–Yang consumers are stated for an abstract `LeeYangDatum`: a polynomial with no
zero on the open polydisk whose reflection has none either. They include the zero-count law, the
first-zero law (`exists_restr_eq_zero`), the integer-anchoring no-go
(`not_tendstoUniformlyOn_leeYang_XiC`) and the field-density budget
(`exists_eventually_fieldDensity_le_gammaDensity`). Before the multivariate Lee–Yang theorem
(`GaloisForLFunctions.HTGeometry.LeeYang.leeYang_polydisc`), concrete data were available only for
chains.

* `isingMvPoly`: the Ising polynomial `Σ_S c_S ∏_{k∈S} u_k` of any graph, as an `MvPolynomial`.
* `degreeOf_isingMvPoly`: every site has degree exactly one, since the all-down monomial has
  coefficient one.
* `dualPoly_isingMvPoly`: the polynomial is self-dual, `P^♯ = P`. This follows from complement
  symmetry and the real coefficients.
* `isingDatum`: with any positive frequencies it is a `LeeYangDatum`.

**Corollaries.** Every ferromagnetic Ising graph with fields `e^{−iλ_k t}`:
* vanishes within `π/λ_j` of the origin, for every site `j` (`isingGraph_exists_zero`);
* gives no normalized family converging to `E·Ξ` on `[−π/log 2, π/log 2]` once some field frequency
  is `≥ log 2` (`not_tendstoUniformlyOn_isingGraph_XiC`);
* obeys the field-density bound `Σ_j max(λ_j − 2π/T, 0) ≤ log(T/2π) − 1 + C/√T` when its normalized
  partition functions converge to `E·Ξ` (`exists_isingGraph_fieldDensity_le`).

**Capstone.** Conversely, if normalized partition functions of Lee–Yang data (in particular of
ferromagnetic Ising graphs, with any positive field frequencies) converge locally uniformly to `E·Ξ`
with `E` entire and zero-free, then RH holds
(`riemannHypothesis_of_leeYangDatum_tendstoLocallyUniformly_mul_XiC`,
`riemannHypothesis_of_isingGraph_tendstoLocallyUniformly_mul_XiC`).
-/

open MvPolynomial Complex Finset
open GaloisForLFunctions.HTGeometry.LeeYang

namespace RHTower.LeeYangCount

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exponent vector of the monomial `∏_{k∈S} u_k`. -/
def indExp (S : Finset V) : V →₀ ℕ := Multiset.toFinsupp S.val

omit [Fintype V] in
theorem indExp_apply (S : Finset V) (k : V) : indExp S k = if k ∈ S then 1 else 0 := by
  rw [indExp, Multiset.toFinsupp_apply]
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem S.nodup h
  · exact Multiset.count_eq_zero.mpr h

omit [Fintype V] in
theorem indExp_injective : Function.Injective (indExp (V := V)) := by
  intro S T h
  ext k
  have := congrArg (fun f : V →₀ ℕ => f k) h
  simp only [indExp_apply] at this
  by_cases hS : k ∈ S <;> by_cases hT : k ∈ T <;> simp_all

/-- The Ising polynomial of a graph as a multivariate polynomial. -/
def isingMvPoly (a : V → V → ℝ) (E : Finset (V × V)) : MvPolynomial V ℂ :=
  ∑ S : Finset V, monomial (indExp S) (isingCoeff a E S)

theorem eval_isingMvPoly (a : V → V → ℝ) (E : Finset (V × V)) (w : V → ℂ) :
    eval w (isingMvPoly a E) = maEval (isingCoeff a E) w := by
  rw [isingMvPoly, map_sum, maEval]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  congr 1
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun k _ hk => by simp [indExp_apply, hk])]
  exact Finset.prod_congr rfl fun k hk => by simp [indExp_apply, hk]

theorem coeff_isingMvPoly (a : V → V → ℝ) (E : Finset (V × V)) (T : Finset V) :
    coeff (indExp T) (isingMvPoly a E) = isingCoeff a E T := by
  rw [isingMvPoly, coeff_sum]
  simp_rw [coeff_monomial, indExp_injective.eq_iff]
  simp

theorem isingCoeff_univ (a : V → V → ℝ) (E : Finset (V × V)) : isingCoeff a E Finset.univ = 1 := by
  simp [isingCoeff, bondWeight]

/-- Every site enters the Ising polynomial with degree exactly one. -/
theorem degreeOf_isingMvPoly (a : V → V → ℝ) (E : Finset (V × V)) (j : V) :
    degreeOf j (isingMvPoly a E) = 1 := by
  apply le_antisymm
  · rw [degreeOf_le_iff]
    intro m hm
    have hsub := MvPolynomial.support_sum hm
    simp only [Finset.mem_biUnion] at hsub
    obtain ⟨S, -, hS⟩ := hsub
    have := support_monomial_subset hS
    rw [Finset.mem_singleton] at this
    rw [this, indExp_apply]; split_ifs <;> omega
  · have hmem : indExp (Finset.univ : Finset V) ∈ (isingMvPoly a E).support := by
      rw [mem_support_iff, coeff_isingMvPoly, isingCoeff_univ]; exact one_ne_zero
    have := monomial_le_degreeOf j hmem
    rwa [indExp_apply, if_pos (Finset.mem_univ j)] at this

omit [Fintype V] in
theorem conj_isingCoeff (a : V → V → ℝ) (E : Finset (V × V)) (S : Finset V) :
    (starRingEnd ℂ) (isingCoeff a E S) = isingCoeff a E S := by
  rw [isingCoeff, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp only [bondWeight]
  split_ifs <;> simp

theorem maEval_conj (a : V → V → ℝ) (E : Finset (V × V)) (w : V → ℂ) :
    maEval (isingCoeff a E) (fun k => (starRingEnd ℂ) (w k)) =
      (starRingEnd ℂ) (maEval (isingCoeff a E) w) := by
  rw [maEval, maEval, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_mul, map_prod, conj_isingCoeff]

/-- `P^♯(w) = P(w)` at every field vector with nonzero coordinates. -/
theorem eval_dualPoly_isingMvPoly_of_ne_zero (a : V → V → ℝ) (E : Finset (V × V)) {w : V → ℂ}
    (hw : ∀ j, w j ≠ 0) :
    eval w (dualPoly (isingMvPoly a E)) = eval w (isingMvPoly a E) := by
  set u : V → ℂ := fun j => ((starRingEnd ℂ) (w j))⁻¹ with hu
  have hu0 : ∀ j, u j ≠ 0 := fun j => inv_ne_zero ((map_ne_zero _).mpr (hw j))
  have hrefl := eval_eq_prod_mul_conj_dual (isingMvPoly a E) hu0
  have hback : (fun j => ((starRingEnd ℂ) (u j))⁻¹) = w := by funext j; simp [hu]
  rw [hback] at hrefl
  simp only [degreeOf_isingMvPoly, pow_one] at hrefl
  have hsym := maEval_eq_prod_mul_inv (isingCoeff_compl a E) hu0
  have hinv : (fun k => (u k)⁻¹) = fun k => (starRingEnd ℂ) (w k) := by funext k; simp [hu]
  rw [hinv, maEval_conj] at hsym
  rw [eval_isingMvPoly] at hrefl
  rw [hrefl] at hsym
  have hprod0 : (∏ j, u j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hu0 j
  have := mul_left_cancel₀ hprod0 hsym
  have h2 := congrArg (starRingEnd ℂ) this
  simp only [Complex.conj_conj] at h2
  rw [h2, eval_isingMvPoly]

/-- **Self-duality** of the Ising polynomial. -/
theorem dualPoly_isingMvPoly (a : V → V → ℝ) (E : Finset (V × V)) :
    dualPoly (isingMvPoly a E) = isingMvPoly a E := by
  have hX : (∏ j : V, (X j : MvPolynomial V ℂ)) ≠ 0 := prod_ne_zero_iff.mpr fun j _ => X_ne_zero j
  apply mul_left_cancel₀ hX
  apply MvPolynomial.funext
  intro w
  rw [map_mul, map_mul, map_prod]
  simp only [eval_X]
  by_cases hw : ∀ j, w j ≠ 0
  · rw [eval_dualPoly_isingMvPoly_of_ne_zero a E hw]
  · push Not at hw
    obtain ⟨j, hj⟩ := hw
    rw [prod_eq_zero (mem_univ j) hj, zero_mul, zero_mul]

/-- **Every ferromagnetic Ising graph is a Lee–Yang datum**, with any positive field frequencies. -/
def isingDatum (a : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (ha : ∀ p ∈ E, |a p.1 p.2| ≤ 1) (freq : V → ℝ) (hfreq : ∀ j, 0 < freq j) :
    LeeYangDatum V where
  P := isingMvPoly a E
  freq := freq
  freq_pos := hfreq
  disk := fun w hw => by rw [eval_isingMvPoly]; exact leeYang_polydisc a E hE ha w hw
  dualDisk := fun w hw => by
    rw [dualPoly_isingMvPoly, eval_isingMvPoly]; exact leeYang_polydisc a E hE ha w hw

theorem isingDatum_degreeOf (a : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (ha : ∀ p ∈ E, |a p.1 p.2| ≤ 1) (freq : V → ℝ) (hfreq : ∀ j, 0 < freq j) (j : V) :
    (isingDatum a E hE ha freq hfreq).P.degreeOf j = 1 :=
  degreeOf_isingMvPoly a E j

/-- **Every site forces a zero.** In a ferromagnetic Ising graph with fields `e^{−iλ_k t}`, the
partition function vanishes at some real `t` with `|t| ≤ π/λ_j`, for every site `j`. -/
theorem isingGraph_exists_zero (a : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (ha : ∀ p ∈ E, |a p.1 p.2| ≤ 1) (freq : V → ℝ) (hfreq : ∀ j, 0 < freq j) (j : V) :
    ∃ t ∈ Set.Icc (-(Real.pi / freq j)) (Real.pi / freq j),
      maEval (isingCoeff a E) (fun k => Complex.exp (-(I * (freq k : ℂ) * (t : ℂ)))) = 0 := by
  obtain ⟨t, ht, h⟩ := (isingDatum a E hE ha freq hfreq).exists_restr_eq_zero j
    (isingDatum_degreeOf a E hE ha freq hfreq j)
  refine ⟨t, ht, ?_⟩
  rw [← eval_isingMvPoly]
  exact h

/-- **No integer-anchored ferromagnetic Ising producer of `Ξ`, on any graph.** Take any family of
ferromagnetic Ising graphs, each with a site whose field frequency is at least `log 2`, and any
normalizations `e_i`. Their partition functions do not converge uniformly on
`[−π/log 2, π/log 2]` to `E·Ξ` with `E` continuous and zero-free. -/
theorem not_tendstoUniformlyOn_isingGraph_XiC {κ : Type*} {l : Filter κ} [l.NeBot]
    {ι : κ → Type*} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (a : ∀ i, ι i → ι i → ℝ) (E : ∀ i, Finset (ι i × ι i))
    (hE : ∀ i, ∀ p ∈ E i, p.1 ≠ p.2) (ha : ∀ i, ∀ p ∈ E i, |a i p.1 p.2| ≤ 1)
    (freq : ∀ i, ι i → ℝ) (hfreq : ∀ i j, 0 < freq i j) (j : ∀ i, ι i)
    (hj : ∀ i, Real.log 2 ≤ freq i (j i)) (e : κ → ℝ → ℂ) {Ef : ℝ → ℂ}
    (hEf : ContinuousOn Ef (Set.Icc (-(Real.pi / Real.log 2)) (Real.pi / Real.log 2)))
    (hEf0 : ∀ t ∈ Set.Icc (-(Real.pi / Real.log 2)) (Real.pi / Real.log 2), Ef t ≠ 0) :
    ¬ TendstoUniformlyOn
      (fun i t => e i t * maEval (isingCoeff (a i) (E i))
        (fun k => Complex.exp (-(I * (freq i k : ℂ) * (t : ℂ)))))
      (fun t => Ef t * XiC (t : ℂ)) l
      (Set.Icc (-(Real.pi / Real.log 2)) (Real.pi / Real.log 2)) := by
  have h := not_tendstoUniformlyOn_leeYang_XiC (l := l)
    (fun i => isingDatum (a i) (E i) (hE i) (ha i) (freq i) (hfreq i)) j
    (fun i => isingDatum_degreeOf _ _ _ _ _ _ (j i)) hj e hEf hEf0
  convert h using 3 with i t
  simp only [LeeYangDatum.restr, LeeYangDatum.field, isingDatum, eval_isingMvPoly]

/-- **Field density of ferromagnetic Ising producers of `Ξ`.** If normalized partition functions of
ferromagnetic Ising graphs converge locally uniformly to `E·Ξ` (`E` entire and zero-free), then
eventually `Σ_j max(λ_j − 2π/T, 0) ≤ log(T/2π) − 1 + C/√T`, with an absolute constant `C`. -/
theorem exists_isingGraph_fieldDensity_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {α : Type*} {p : Filter α} {ι : α → Type*} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
      (a : ∀ i, ι i → ι i → ℝ) (E : ∀ i, Finset (ι i × ι i)),
      (∀ i, ∀ q ∈ E i, q.1 ≠ q.2) → (∀ i, ∀ q ∈ E i, |a i q.1 q.2| ≤ 1) →
      ∀ (freq : ∀ i, ι i → ℝ), (∀ i j, 0 < freq i j) → ∀ (κ : α → ℂ), (∀ i, κ i ≠ 0) →
      ∀ {Ef : ℂ → ℂ}, Differentiable ℂ Ef → (∀ z, Ef z ≠ 0) →
      TendstoLocallyUniformly
        (fun i z => κ i * maEval (isingCoeff (a i) (E i))
          (fun k => Complex.exp (-(I * (freq i k : ℂ) * z))))
        (fun z => Ef z * XiC z) p →
      ∀ {T η : ℝ}, 4 ≤ T → 0 < η → η ≤ 1 →
      (∀ z ∈ Metric.sphere ((T : ℂ) / 2) (T / 2 + η), Ef z * XiC z ≠ 0) →
      ∀ᶠ i in p, ∑ j, max (freq i j - 2 * Real.pi / T) 0 ≤
        Real.log (T / (2 * Real.pi)) - 1 + C / Real.sqrt T := by
  obtain ⟨C, hC, h⟩ := exists_eventually_fieldDensity_le_gammaDensity
  refine ⟨C, hC, ?_⟩
  intro α p ι _ _ a E hE ha freq hfreq κ hκ Ef hEf hEf0 hconv T η hT hη hη1 hsph
  have hconv' : TendstoLocallyUniformly
      (fun i z => κ i * (isingDatum (a i) (E i) (hE i) (ha i) (freq i) (hfreq i)).restr z)
      (fun z => Ef z * XiC z) p := by
    convert hconv using 3 with i z
    simp only [LeeYangDatum.restr, LeeYangDatum.field, isingDatum, eval_isingMvPoly]
  exact h (fun i => isingDatum (a i) (E i) (hE i) (ha i) (freq i) (hfreq i))
    (fun i j => isingDatum_degreeOf _ _ _ _ _ _ j) κ hκ hEf hEf0 hconv' hT hη hη1 hsph

/-- **Lee–Yang capstone.** If normalized restrictions of Lee–Yang data converge locally uniformly to
`E·Ξ`, with `E` entire and zero-free, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_leeYangDatum_tendstoLocallyUniformly_mul_XiC
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (L : ∀ n, LeeYangDatum (ι n)) (κ : ℕ → ℂ)
    (hκ : ∀ n, κ n ≠ 0) {Ef : ℂ → ℂ} (hEf : AnalyticOnNhd ℂ Ef Set.univ) (hEf0 : ∀ z, Ef z ≠ 0)
    (hconv : TendstoLocallyUniformly (fun n z => κ n * (L n).restr z) (fun z => Ef z * XiC z)
      Filter.atTop) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have him : z.im = 0 := zero_mem_closed_of_tendstoLocallyUniformly hconv
    (hEf.mul XiC_analytic)
    (Filter.Eventually.of_forall fun n => ((L n).differentiable_restr).const_mul (κ n))
    (isClosed_eq Complex.continuous_im continuous_const)
    (Filter.Eventually.of_forall fun n w hw =>
      (L n).restr_im_eq_zero_of_eq_zero ((mul_eq_zero.mp hw).resolve_left (hκ n)))
    (mul_ne_zero (hEf0 0) XiC_zero_ne) (by simp [hXiC])
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  exact (ne_of_gt (mem_rightHalf.mp hρ)) (by linarith)

/-- **Ising graph capstone.** If normalized partition functions of ferromagnetic Ising graphs, with
any graphs, couplings `|a| ≤ 1` and positive field frequencies, converge locally uniformly to `E·Ξ`
with `E` entire and zero-free, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_isingGraph_tendstoLocallyUniformly_mul_XiC
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (a : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hE : ∀ n, ∀ q ∈ E n, q.1 ≠ q.2) (ha : ∀ n, ∀ q ∈ E n, |a n q.1 q.2| ≤ 1)
    (freq : ∀ n, ι n → ℝ) (hfreq : ∀ n j, 0 < freq n j) (κ : ℕ → ℂ) (hκ : ∀ n, κ n ≠ 0)
    {Ef : ℂ → ℂ} (hEf : AnalyticOnNhd ℂ Ef Set.univ) (hEf0 : ∀ z, Ef z ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n z => κ n * maEval (isingCoeff (a n) (E n))
        (fun k => Complex.exp (-(I * (freq n k : ℂ) * z))))
      (fun z => Ef z * XiC z) Filter.atTop) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_leeYangDatum_tendstoLocallyUniformly_mul_XiC
    (fun n => isingDatum (a n) (E n) (hE n) (ha n) (freq n) (hfreq n)) κ hκ hEf hEf0 ?_
  convert hconv using 3 with n z
  simp only [LeeYangDatum.restr, LeeYangDatum.field, isingDatum, eval_isingMvPoly]

end

end RHTower.LeeYangCount
