import GaloisForLFunctions.RHTower.ChiRamanujanCompleteCubicTrace
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Finsupp.Basic

/-!
# Full valuation-lattice cubic sum and dilation orthogonality

Absolute Euler control promotes finite-prime traces to one unconditional sum
on finitely supported integer prime valuations. The complete cubic and its
absolute mass are evaluated, and every nonzero prime dilation is orthogonal
to the actual coefficient. Identification with positive rational coefficients
and the physical prime cubic are separate obligations.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace RHTower.BAGTrace

def localDilation (z : ℝ) (j i : ℤ) : ℝ :=
  coefficient z i * coefficient z (i+j) * z^i

theorem localDilation_pos_decomposition {z : ℝ} (hz : z ≠ 0) {j : ℤ} (hj : 0 < j)
    (i : ℤ) : localDilation z j i = geometric z i - (1-z)⁻¹*atom (-1) i := by
  by_cases hi : i = -1
  · subst i
    have h0 : (0 : ℤ) ≤ -1+j := by omega
    have h1 : (-1 : ℤ)+j ≠ -1 := by omega
    simp [localDilation,coefficient,geometric,atom,h0,h1]
    field_simp
  · by_cases hi0 : 0 ≤ i
    · have hij : 0 ≤ i+j := by omega
      have hij1 : i+j ≠ -1 := by omega
      simp [localDilation,coefficient,geometric,atom,hi,hi0,hij,hij1]
    · simp [localDilation,coefficient,geometric,atom,hi,hi0]

theorem localDilation_hasSum_pos {z : ℝ} (hz : 0 < z) (hz1 : z < 1)
    {j : ℤ} (hj : 0 < j) : HasSum (localDilation z j) 0 := by
  have h := (geometric_hasSum (show |z| < 1 by rwa [abs_of_pos hz])).sub
    ((atom_hasSum (-1)).mul_left (1-z)⁻¹)
  simp only [mul_one,sub_self] at h
  exact h.congr_fun (fun i => localDilation_pos_decomposition hz.ne' hj i)

theorem localDilation_zero_decomposition {z : ℝ} (hz : z ≠ 0) (i : ℤ) :
    localDilation z 0 i = geometric z i + z/(1-z)^2*atom (-1) i := by
  by_cases hi : i = -1
  · subst i
    simp [localDilation,coefficient,geometric,atom]
    field_simp
  · by_cases hi0 : 0 ≤ i <;>
      simp [localDilation,coefficient,geometric,atom,hi,hi0]

theorem localDilation_hasSum_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    HasSum (localDilation z 0) ((1-z)⁻¹^2) := by
  have h := (geometric_hasSum (show |z| < 1 by rwa [abs_of_pos hz])).add
    ((atom_hasSum (-1)).mul_left (z/(1-z)^2))
  have he : (1-z)⁻¹+z/(1-z)^2*1=(1-z)⁻¹^2 := by
    have hd : 1-z ≠ 0 := ne_of_gt (sub_pos.mpr hz1)
    field_simp
    ring
  rw [he] at h
  exact h.congr_fun (fun i => localDilation_zero_decomposition hz.ne' i)

theorem localDilation_neg_translation {z : ℝ} (hz : z ≠ 0) (j i : ℤ) :
    z^(-j)*localDilation z (-j) (i+j) = localDilation z j i := by
  simp only [localDilation,add_neg_cancel_right,zpow_add₀ hz]
  rw [zpow_neg]
  have hj : z^j ≠ 0 := zpow_ne_zero _ hz
  field_simp

theorem localDilation_hasSum {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (j : ℤ) :
    HasSum (localDilation z j) (if j=0 then (1-z)⁻¹^2 else 0) := by
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · have h := ((Equiv.addRight j).hasSum_iff).mpr
      (localDilation_hasSum_pos hz hz1 (j := -j) (by omega))
    have ht := h.mul_left (z^(-j))
    simp only [mul_zero] at ht
    rw [if_neg (ne_of_lt hj)]
    exact ht.congr_fun (fun i => (localDilation_neg_translation hz.ne' j i).symm)
  · simpa using localDilation_hasSum_zero hz hz1
  · simpa only [if_neg (ne_of_gt hj)] using localDilation_hasSum_pos hz hz1 hj


def primeSupportCut {α X : Type} [Zero X] (f : (α →₀ X) → ℝ)
    (P : Finset α) : (α →₀ X) → ℝ := {v | v.support ⊆ P}.indicator f

def supportedCoordinates {α X : Type} [AddCommMonoid X] (P : Finset α) :
    {v : α →₀ X // v.support ⊆ P} ≃ (P → X) :=
  (Equiv.subtypeEquivRight (fun _ => Finset.coe_subset.symm)).trans
    ((Finsupp.restrictSupportEquiv (P : Set α) X).trans Finsupp.equivFunOnFinite)

theorem supportedCoordinates_apply {α X : Type} [AddCommMonoid X]
    (P : Finset α) (v : {v : α →₀ X // v.support ⊆ P}) (p : P) :
    supportedCoordinates P v p = v.1 p := rfl

theorem finite_finsupp_product_hasSum {α X : Type} [AddCommMonoid X]
    (P : Finset α) (f : α → X → ℝ) (L : α → ℝ)
    (hf0 : ∀ p, f p 0=1) (hlocal : ∀ p, HasSum (f p) (L p)) :
    HasSum (primeSupportCut (fun v : α →₀ X => v.prod f) P) (∏ p ∈ P,L p) := by
  classical
  have h := finite_product_hasSum P (fun p => f p) (fun p => L p) (fun p => hlocal p)
  have hs := ((supportedCoordinates (X := X) P).hasSum_iff).mpr h
  have hs' : HasSum (fun v : {v : α →₀ X // v.support ⊆ P} => v.1.prod f)
      (∏ p : P,L p) := by
    apply hs.congr_fun
    intro v
    rw [v.1.prod_of_support_subset v.2 f (fun p _ => hf0 p)]
    exact (Finset.prod_coe_sort P (fun p => f p (v.1 p))).symm
  rw [Finset.prod_coe_sort] at hs'
  exact hasSum_subtype_iff_indicator.mp hs'

theorem summable_norm_of_supportCut_limit {α X : Type} [Zero X]
    {f : (α →₀ X) → ℝ} {L : ℝ}
    (hcut : ∀ P : Finset α, Summable (fun v => ‖primeSupportCut f P v‖))
    (hlim : Tendsto (fun P : Finset α => ∑' v, ‖primeSupportCut f P v‖) atTop (𝓝 L)) :
    Summable (fun v => ‖f v‖) := by
  classical
  obtain ⟨P₀,hP₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (lt_add_one L)))
  apply summable_of_sum_le (fun v => norm_nonneg (f v)) (c := L+1)
  intro F
  let P := P₀ ∪ F.biUnion Finsupp.support
  have hvP (v : α →₀ X) (hv : v ∈ F) : v.support ⊆ P :=
    (Finset.subset_biUnion_of_mem Finsupp.support hv).trans Finset.subset_union_right
  calc
    ∑ v ∈ F, ‖f v‖ = ∑ v ∈ F, ‖primeSupportCut f P v‖ := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [primeSupportCut,hvP v hv]
    _ ≤ ∑' v, ‖primeSupportCut f P v‖ :=
      (hcut P).sum_le_tsum F (fun v _ => norm_nonneg _)
    _ ≤ L+1 := (hP₀ P Finset.subset_union_left).le

theorem tendsto_tsum_primeSupportCut {α X : Type} [Zero X]
    {f : (α →₀ X) → ℝ} (hf : Summable (fun v => ‖f v‖)) :
    Tendsto (fun P : Finset α => ∑' v, primeSupportCut f P v) atTop (𝓝 (∑' v,f v)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence hf
  · intro v
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop v.support] with P hP
    simp [primeSupportCut,hP]
  · exact Eventually.of_forall fun P v => by
      by_cases h : v.support ⊆ P <;> simp [primeSupportCut,h]

theorem finsupp_product_hasSum {α X : Type} [AddCommMonoid X]
    (f : α → X → ℝ) (L A : α → ℝ) {s t : ℝ}
    (hf0 : ∀ p, f p 0=1) (hlocal : ∀ p, HasSum (f p) (L p))
    (habs : ∀ p, HasSum (fun i => |f p i|) (A p))
    (hprod : HasProd L s) (haprod : HasProd A t) :
    HasSum (fun v : α →₀ X => v.prod f) s := by
  classical
  have he (P : Finset α) (v : α →₀ X) :
      ‖primeSupportCut (fun v => v.prod f) P v‖ =
      primeSupportCut (fun v => v.prod (fun p i => |f p i|)) P v := by
    by_cases hv : v.support ⊆ P
    · simp [primeSupportCut,hv,Finsupp.prod,Real.norm_eq_abs]
    · simp [primeSupportCut,hv]
  have hcut (P : Finset α) : HasSum
      (fun v : α →₀ X => ‖primeSupportCut (fun v => v.prod f) P v‖) (∏ p ∈ P,A p) := by
    simp_rw [he]
    exact finite_finsupp_product_hasSum P _ A (by intro p; rw [hf0]; exact abs_one) habs
  have hn : Summable (fun v : α →₀ X => ‖v.prod f‖) := by
    apply summable_norm_of_supportCut_limit (L := t) (fun P => (hcut P).summable)
    change Tendsto (fun P : Finset α => ∏ p ∈ P,A p) atTop (𝓝 t) at haprod
    simpa only [(hcut _).tsum_eq] using haprod
  have htotal := tendsto_tsum_primeSupportCut hn
  have hsame : Tendsto (fun P : Finset α => ∑' v, primeSupportCut (fun v => v.prod f) P v)
      atTop (𝓝 s) := by
    change Tendsto (fun P : Finset α => ∏ p ∈ P,L p) atTop (𝓝 s) at hprod
    simpa only [(finite_finsupp_product_hasSum _ f L hf0 hlocal).tsum_eq] using hprod
  have heq : (∑' v : α →₀ X,v.prod f)=s := tendsto_nhds_unique htotal hsame
  rw [← heq]
  exact hn.of_norm.hasSum

private theorem primeWeight_lt_one {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) :
    primeWeight σ p < 1 := lt_of_le_of_lt (primeWeight_le_half hσ p) (by norm_num)

private theorem primeSquare_hasProd {σ : ℝ} (hσ : 1 < σ) :
    HasProd (fun p : Nat.Primes => (1-primeWeight σ p)⁻¹^2) ((riemannZeta (σ : ℂ)).re^2) := by
  change Tendsto (fun P : Finset Nat.Primes => ∏ p ∈ P,(1-primeWeight σ p)⁻¹^2)
    atTop (𝓝 ((riemannZeta (σ : ℂ)).re^2))
  exact (complete_signed_trace_zeta hσ).congr (fun P => trace_eq hσ P)

private theorem primeAbsoluteCubic_hasProd {σ : ℝ} (hσ : 1 < σ) :
    HasProd (fun p : Nat.Primes => (1+4*primeWeight σ p)/(1-primeWeight σ p)^2)
      ((riemannZeta (σ : ℂ)).re^2 * ∏' p, (1+4*primeWeight σ p)) := by
  change Tendsto (fun P : Finset Nat.Primes => ∏ p ∈ P,
    (1+4*primeWeight σ p)/(1-primeWeight σ p)^2) atTop _
  exact (complete_absolute_trace_limit hσ).congr (fun P => absoluteTrace_eq hσ P)

def valuationCubic (σ : ℝ) (v : Nat.Primes →₀ ℤ × ℤ) : ℝ :=
  v.prod (fun p => localTriple (primeWeight σ p))

/-- A single unordered, absolutely convergent sum over the full prime-valuation lattice. -/
theorem valuationCubic_hasSum {σ : ℝ} (hσ : 1 < σ) :
    HasSum (valuationCubic σ) ((riemannZeta (σ : ℂ)).re^2) := by
  apply finsupp_product_hasSum _ _ _
    (fun p => by simp [localTriple,coefficient])
    (fun p => localTriple_hasSum (primeWeight_pos σ p) (primeWeight_lt_one hσ p))
    (fun p => localTriple_abs_hasSum (primeWeight_pos σ p) (primeWeight_lt_one hσ p))
    (primeSquare_hasProd hσ) (primeAbsoluteCubic_hasProd hσ)

theorem valuationCubic_abs_hasSum {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun v => |valuationCubic σ v|)
      ((riemannZeta (σ : ℂ)).re^2 * ∏' p, (1+4*primeWeight σ p)) := by
  have h := finsupp_product_hasSum (fun p v => |localTriple (primeWeight σ p) v|)
    _ _ (fun p => by simp [localTriple,coefficient])
    (fun p => localTriple_abs_hasSum (primeWeight_pos σ p) (primeWeight_lt_one hσ p))
    (fun p => by simpa only [abs_abs] using
      localTriple_abs_hasSum (primeWeight_pos σ p) (primeWeight_lt_one hσ p))
    (primeAbsoluteCubic_hasProd hσ) (primeAbsoluteCubic_hasProd hσ)
  exact h.congr_fun (fun v => by simp [valuationCubic,Finsupp.prod,Finset.abs_prod])

abbrev PrimeValuations := Nat.Primes →₀ ℤ

def valuationCoefficient (σ : ℝ) (v : PrimeValuations) : ℝ :=
  v.prod (fun p i => coefficient (primeWeight σ p) i)

def valuationWeight (σ : ℝ) (v : PrimeValuations) : ℝ :=
  v.prod (fun p i => primeWeight σ p ^ i)

def valuationEnergy (σ : ℝ) (v : PrimeValuations) : ℝ :=
  valuationCoefficient σ v ^ 2 * valuationWeight σ v

theorem valuationWeight_pos (σ : ℝ) (v : PrimeValuations) : 0 < valuationWeight σ v := by
  exact Finset.prod_pos (fun p _ => zpow_pos (primeWeight_pos σ p) _)

theorem valuationWeight_add (σ : ℝ) (v j : PrimeValuations) :
    valuationWeight σ (v+j)=valuationWeight σ v * valuationWeight σ j := by
  exact Finsupp.prod_add_index' (fun p => zpow_zero _)
    (fun p i k => zpow_add₀ (primeWeight_pos σ p).ne' _ _)

theorem valuationEnergy_prod (σ : ℝ) (v : PrimeValuations) :
    valuationEnergy σ v = v.prod (fun p i => localDilation (primeWeight σ p) 0 i) := by
  simp only [valuationEnergy,valuationCoefficient,valuationWeight,Finsupp.prod,
    localDilation,add_zero,← Finset.prod_mul_distrib,pow_two]

theorem valuationEnergy_nonneg (σ : ℝ) (v : PrimeValuations) : 0 ≤ valuationEnergy σ v :=
  mul_nonneg (sq_nonneg _) (valuationWeight_pos σ v).le

theorem valuationEnergy_hasSum {σ : ℝ} (hσ : 1 < σ) :
    HasSum (valuationEnergy σ) ((riemannZeta (σ : ℂ)).re^2) := by
  have habs (p : Nat.Primes) : HasSum
      (fun i => |localDilation (primeWeight σ p) 0 i|) ((1-primeWeight σ p)⁻¹^2) := by
    have h := localDilation_hasSum_zero (primeWeight_pos σ p) (primeWeight_lt_one hσ p)
    apply h.congr_fun
    intro i
    apply abs_of_nonneg
    simpa only [localDilation,add_zero,← pow_two] using
      mul_nonneg (sq_nonneg (coefficient (primeWeight σ p) i))
        (zpow_pos (primeWeight_pos σ p) i).le
  have h := finsupp_product_hasSum (fun p => localDilation (primeWeight σ p) 0)
    _ _ (fun p => by simp [localDilation,coefficient])
    (fun p => localDilation_hasSum_zero (primeWeight_pos σ p) (primeWeight_lt_one hσ p))
    habs (primeSquare_hasProd hσ) (primeSquare_hasProd hσ)
  exact h.congr_fun (fun v => valuationEnergy_prod σ v)

def valuationDilation (σ : ℝ) (j v : PrimeValuations) : ℝ :=
  valuationCoefficient σ v * valuationCoefficient σ (v+j) * valuationWeight σ v

theorem norm_valuationDilation_le (σ : ℝ) (j v : PrimeValuations) :
    ‖valuationDilation σ j v‖ ≤ valuationEnergy σ v +
      (valuationWeight σ j)⁻¹*valuationEnergy σ (v+j) := by
  have hw := valuationWeight_pos σ v
  have hj := valuationWeight_pos σ j
  have hab : |valuationCoefficient σ v| * |valuationCoefficient σ (v+j)| ≤
      valuationCoefficient σ v^2+valuationCoefficient σ (v+j)^2 := by
    nlinarith [sq_nonneg (|valuationCoefficient σ v|-|valuationCoefficient σ (v+j)|),
      sq_abs (valuationCoefficient σ v),sq_abs (valuationCoefficient σ (v+j)),
      sq_nonneg (valuationCoefficient σ v),sq_nonneg (valuationCoefficient σ (v+j))]
  rw [valuationDilation,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos hw]
  calc
    _ ≤ (valuationCoefficient σ v^2+valuationCoefficient σ (v+j)^2)*valuationWeight σ v :=
      mul_le_mul_of_nonneg_right hab hw.le
    _ = _ := by
      rw [valuationEnergy,valuationEnergy,valuationWeight_add]
      field_simp

theorem summable_norm_valuationDilation {σ : ℝ} (hσ : 1 < σ) (j : PrimeValuations) :
    Summable (fun v => ‖valuationDilation σ j v‖) := by
  have h := (valuationEnergy_hasSum hσ).summable
  have hshift : Summable (fun v => valuationEnergy σ (v+j)) :=
    h.comp_injective (Equiv.addRight j).injective
  apply (h.add (hshift.mul_left (valuationWeight σ j)⁻¹)).of_norm_bounded
  intro v
  rw [norm_norm]
  exact norm_valuationDilation_le σ j v

theorem valuationDilation_prod_on (σ : ℝ) (j v : PrimeValuations) (P : Finset Nat.Primes)
    (hv : v.support ⊆ P) (hj : j.support ⊆ P) :
    valuationDilation σ j v = ∏ p ∈ P,localDilation (primeWeight σ p) (j p) (v p) := by
  classical
  have hs : (v+j).support ⊆ P := Finsupp.support_add.trans (Finset.union_subset hv hj)
  unfold valuationDilation valuationCoefficient valuationWeight
  rw [v.prod_of_support_subset hv _ (fun p _ => by simp [coefficient]),
    (v+j).prod_of_support_subset hs _ (fun p _ => by simp [coefficient]),
    v.prod_of_support_subset hv _ (fun p _ => zpow_zero _)]
  simp only [← Finset.prod_mul_distrib,localDilation,Finsupp.add_apply]

private theorem valuationDilation_cut_product_hasSum {σ : ℝ} (hσ : 1 < σ) (j : PrimeValuations)
    (P : Finset Nat.Primes) (hjP : j.support ⊆ P) :
    HasSum (primeSupportCut (valuationDilation σ j) P)
      (∏ p ∈ P,if j p=0 then (1-primeWeight σ p)⁻¹^2 else 0) := by
  classical
  have h := finite_product_hasSum P (fun p => localDilation (primeWeight σ p) (j p))
    (fun p => if j p=0 then (1-primeWeight σ p)⁻¹^2 else 0)
    (fun p => localDilation_hasSum (primeWeight_pos σ p) (primeWeight_lt_one hσ p) (j p))
  have hs := ((supportedCoordinates (X := ℤ) P).hasSum_iff).mpr h
  have hs' : HasSum (fun v : {v : PrimeValuations // v.support ⊆ P} => valuationDilation σ j v.1)
      (∏ p : P, if j p=0 then (1-primeWeight σ p)⁻¹^2 else 0) := by
    apply hs.congr_fun
    intro v
    rw [valuationDilation_prod_on σ j v.1 P v.2 hjP]
    exact (Finset.prod_coe_sort P (fun p => localDilation (primeWeight σ p) (j p) (v.1 p))).symm
  rw [Finset.prod_coe_sort P (fun p => if j p=0 then (1-primeWeight σ p)⁻¹^2 else 0)] at hs'
  exact hasSum_subtype_iff_indicator.mp hs'

private theorem valuationDilation_local_prod (σ : ℝ) (j : PrimeValuations)
    (P : Finset Nat.Primes) (hjP : j.support ⊆ P) :
    (∏ p ∈ P,if j p=0 then (1-primeWeight σ p)⁻¹^2 else 0) =
      if j=0 then ∏ p ∈ P,(1-primeWeight σ p)⁻¹^2 else 0 := by
  classical
  by_cases hj : j=0
  · subst j
    simp
  · rw [if_neg hj]
    obtain ⟨p,hp⟩ : ∃ p,j p ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hj (Finsupp.ext hn)
    exact Finset.prod_eq_zero (hjP (Finsupp.mem_support_iff.mpr hp)) (if_neg hp)

theorem valuationDilation_cut_hasSum {σ : ℝ} (hσ : 1 < σ) (j : PrimeValuations)
    (P : Finset Nat.Primes) (hjP : j.support ⊆ P) :
    HasSum (primeSupportCut (valuationDilation σ j) P)
      (if j=0 then ∏ p ∈ P,(1-primeWeight σ p)⁻¹^2 else 0) := by
  have h := valuationDilation_cut_product_hasSum hσ j P hjP
  rw [valuationDilation_local_prod σ j P hjP] at h
  exact h

/-- Every nonzero finitely supported prime dilation is exactly orthogonal to the full source.
The summability premise is proved from the actual square-energy Euler sum. -/
theorem valuationDilation_hasSum {σ : ℝ} (hσ : 1 < σ) (j : PrimeValuations) :
    HasSum (valuationDilation σ j) (if j=0 then (riemannZeta (σ : ℂ)).re^2 else 0) := by
  classical
  have hn := summable_norm_valuationDilation hσ j
  have ht := tendsto_tsum_primeSupportCut hn
  have hl : Tendsto (fun P : Finset Nat.Primes => ∑' v,primeSupportCut (valuationDilation σ j) P v)
      atTop (𝓝 (if j=0 then (riemannZeta (σ : ℂ)).re^2 else 0)) := by
    by_cases hj : j=0
    · subst j
      rw [if_pos rfl]
      have hp := primeSquare_hasProd hσ
      change Tendsto (fun P : Finset Nat.Primes => ∏ p ∈ P,(1-primeWeight σ p)⁻¹^2)
        atTop (𝓝 ((riemannZeta (σ : ℂ)).re^2)) at hp
      apply hp.congr'
      exact Eventually.of_forall fun P => by
        simpa using (valuationDilation_cut_hasSum hσ 0 P (by simp)).tsum_eq.symm
    · rw [if_neg hj]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop j.support] with P hP
      simpa only [if_neg hj] using (valuationDilation_cut_hasSum hσ j P hP).tsum_eq.symm
  have he := tendsto_nhds_unique ht hl
  rw [← he]
  exact hn.of_norm.hasSum

end RHTower.BAGTrace
