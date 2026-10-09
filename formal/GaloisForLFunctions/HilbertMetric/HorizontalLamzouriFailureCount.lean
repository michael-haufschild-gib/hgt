import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriHybridInterference

/-!
# Counting the mixed points that fail the odd-angle criterion

**Weighted failure-tolerant count**
(`HorizontalPacket.four_mass_sub_energy_le_add_card_fail_weighted`). Every mixed point owns a
pair in a set `O`, and the owners carry weights `w ≥ 0` with `Σ_{q∈O} w_q = 1`. A mixed point `x`
is *certified* when `‖f_x‖² − ½ ≤ w_{own x}·⟪Φ_{own x}⁺ f_x, f_x⟫` (for every diagonalisation).
If all mixed vectors have norm at most `1`, then
`4·mass − E − 2N ≤ #H + #{uncertified mixed points}`.
Each failure costs at most `1`. Uniform weights `1/#O` give
`four_mass_sub_energy_le_add_card_fail`. Owner costs `β ≥ 0` with `Σ_O β ≤ 1` suffice
(`four_mass_sub_energy_le_add_card_fail_budget`). All mixed points are certified as soon as
`Σ_q max_{own x = q} (‖f_x‖² − ½)⁺/⟪Φ_q⁺ f_x, f_x⟫ ≤ 1`.

**Hybrid certificate** (`HorizontalPacket.positivePartForm_owner_ge_of_hybrid`). Split the pairs
into a large set `L` and the rest. Let `κ` bound the angle between `g_p` and `span{h_q : q ∈ L}`,
and let `σ²` bound `Σ_{q∉L} 2m_q(|⟪h_q, g_p⟫| + ‖h_q‖κ)²`. Then
`⟪Φ_p⁺ f, f⟫ ≥ 2m_p((|⟪g_p, f⟫| − (κ + √(σ²/(4λ₀)))‖f‖)⁺)²`,
with `λ₀ = 2m_p(‖g_p‖² − κ²) − σ²/(‖g_p‖² − κ²)`.

**Chebyshev count** (`card_filter_lt_le_sum_sq_div`). If `b > 0`, then
`#{x : a_x > b_x} ≤ Σ_x (a_x/b_x)²`. With `a_x` the interference
`K_x = κ_x + √(σ²_x/(4λ₀_x))` and `b_x` the slack `θ_x` of the certificate,
`HorizontalPacket.four_mass_sub_energy_le_add_hybrid_count` gives
`4·mass − E − 2N ≤ #H + Σ_x (K_x/θ_x)²`.
-/

open scoped RealInnerProductSpace
open Finset Module

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Chebyshev count.** `#{x ∈ s : b x < a x} ≤ Σ_{x∈s} (a x / b x)²` when `b > 0` on `s`. -/
theorem card_filter_lt_le_sum_sq_div {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (hb : ∀ x ∈ s, 0 < b x) :
    ((s.filter fun x => b x < a x).card : ℝ) ≤ ∑ x ∈ s, (a x / b x) ^ 2 := by
  classical
  calc ((s.filter fun x => b x < a x).card : ℝ)
      = ∑ x ∈ s.filter (fun x => b x < a x), (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ s.filter (fun x => b x < a x), (a x / b x) ^ 2 := by
        refine Finset.sum_le_sum fun x hx => ?_
        obtain ⟨hxs, hlt⟩ := Finset.mem_filter.mp hx
        have hbx := hb x hxs
        have h1 : 1 < a x / b x := (one_lt_div hbx).mpr hlt
        nlinarith
    _ ≤ ∑ x ∈ s, (a x / b x) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun x _ _ => sq_nonneg _

namespace HorizontalPacket

variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
  [DecidableEq ιP] [DecidableEq ιM]
variable (P : HorizontalPacket V ι₂ ιH ιM ιP)

/-- A mixed point is *certified with owner weights `w`* when every diagonalisation of its owner
form gives `‖f_x‖² − ½ ≤ w_{own x}·⟪Φ_{own x}⁺ f_x, f_x⟫`. -/
def CertifiedWith (own : ιM → ιP) (w : ιP → ℝ) (x : ιM) : Prop :=
  ∀ (n : ℕ) (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ),
    (∀ v, P.ownerForm (own x) v = ∑ j, ev j * ⟪e j, v⟫ ^ 2) →
      ‖P.fM x‖ ^ 2 - 1 / 2 ≤ w (own x) * positivePartForm e ev (P.fM x)

/-- A mixed point is *certified* when every diagonalisation of its owner form gives
`r(‖f_x‖² − ½) ≤ ⟪Φ_{own x}⁺ f_x, f_x⟫`. -/
def Certified (own : ιM → ιP) (r : ℝ) (x : ιM) : Prop :=
  ∀ (n : ℕ) (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ),
    (∀ v, P.ownerForm (own x) v = ∑ j, ev j * ⟪e j, v⟫ ^ 2) →
      r * (‖P.fM x‖ ^ 2 - 1 / 2) ≤ positivePartForm e ev (P.fM x)

omit [Fintype ι₂] [Fintype ιH] [Fintype ιM] [DecidableEq ιP] [DecidableEq ιM] in
theorem exists_ownerForm_diag [FiniteDimensional ℝ V] (q : ιP) :
    ∃ e : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V, ∃ ev : Fin (finrank ℝ V) → ℝ,
      ∀ v, P.ownerForm q v = ∑ j, ev j * ⟪e j, v⟫ ^ 2 := by
  obtain ⟨e, ev, h⟩ := exists_weightedForm_diag
    (Sum.elim (fun _ : Unit => 2 * P.mP q) fun q' => -(2 * P.mP q'))
    (Sum.elim (fun _ : Unit => P.g q) P.h)
  refine ⟨e, ev, fun v => ?_⟩
  rw [← h, ownerForm]
  simp only [weightedForm, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.univ_unique, Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **Weighted failure-tolerant count.** For owner weights `w ≥ 0` on `O` with `Σ_{q∈O} w_q = 1`,
`4·mass − E − 2N ≤ #H + #{mixed points not certified with weights w}`. -/
theorem four_mass_sub_energy_le_add_card_fail_weighted [FiniteDimensional ℝ V]
    (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ q, 1 ≤ P.mP q) (hH : ∀ i, ‖P.fH i‖ ≤ 1)
    (hMn : ∀ x, ‖P.fM x‖ ≤ 1) (own : ιM → ιP) (O : Finset ιP) (hO : ∀ x, own x ∈ O)
    (w : ιP → ℝ) (hw0 : ∀ q ∈ O, 0 ≤ w q) (hw1 : ∑ q ∈ O, w q = 1)
    (good : Finset ιM) (hgood : ∀ x ∈ good, P.CertifiedWith own w x) :
    4 * P.mass - P.energy - 2 * P.count ≤
      (Fintype.card ιH : ℝ) + (Finset.univ \ good).card := by
  classical
  choose E Ev hE using P.exists_ownerForm_diag
  set Pp : ιP → ιM → ℝ := fun q x => positivePartForm (E q) (Ev q) (P.fM x) with hPp
  set R := ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) + ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) with hR
  set A := 4 * P.mass - P.energy - 2 * P.count with hA
  have hone : ∀ q, A + 2 * ∑ x, Pp q x ≤ R := fun q =>
    P.four_mass_bound_singleOwner hm₂ hmP q (E q) (Ev q) (hE q)
  have hsum : A + 2 * ∑ x, ∑ q ∈ O, w q * Pp q x ≤ R := by
    have h1 := Finset.sum_le_sum fun q (hq : q ∈ O) =>
      mul_le_mul_of_nonneg_left (hone q) (hw0 q hq)
    have h2 : ∑ q ∈ O, w q * (A + 2 * ∑ x, Pp q x) =
        A + 2 * ∑ x, ∑ q ∈ O, w q * Pp q x := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
      congr 1
      have e1 : ∀ q, w q * (2 * ∑ x, Pp q x) = ∑ x, 2 * (w q * Pp q x) := fun q => by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [Finset.sum_congr rfl fun q _ => e1 q, Finset.sum_comm]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
    have h3 : ∑ q ∈ O, w q * R = R := by rw [← Finset.sum_mul, hw1, one_mul]
    linarith
  have hPp0 : ∀ q x, 0 ≤ Pp q x := fun q x => positivePartForm_nonneg _ _ _
  -- certified points are paid by their owner, the others cost at most `1`
  have hpoint : ∀ x, 2 * ‖P.fM x‖ ^ 2 - 1 ≤
      2 * ∑ q ∈ O, w q * Pp q x + (if x ∈ good then 0 else 1) := by
    intro x
    have hsum0 : 0 ≤ ∑ q ∈ O, w q * Pp q x :=
      Finset.sum_nonneg fun q hq => mul_nonneg (hw0 q hq) (hPp0 q x)
    by_cases hx : x ∈ good
    · rw [if_pos hx, add_zero]
      have h1 : ‖P.fM x‖ ^ 2 - 1 / 2 ≤ w (own x) * Pp (own x) x :=
        hgood x hx _ (E (own x)) (Ev (own x)) (hE (own x))
      have h2 : w (own x) * Pp (own x) x ≤ ∑ q ∈ O, w q * Pp q x :=
        Finset.single_le_sum (fun q hq => mul_nonneg (hw0 q hq) (hPp0 q x)) (hO x)
      linarith
    · rw [if_neg hx]
      have := hMn x
      nlinarith [norm_nonneg (P.fM x)]
  have hMsum : ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) ≤
      2 * ∑ x, ∑ q ∈ O, w q * Pp q x + (Finset.univ \ good).card := by
    have h1 := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpoint x
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    have h2 : ∑ x : ιM, (if x ∈ good then (0 : ℝ) else 1) = (Finset.univ \ good).card := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
        mul_one]
      congr 2
      ext x; simp
    rw [h2] at h1
    exact h1
  have hHsum : ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) ≤ (Fintype.card ιH : ℝ) := by
    have : ∀ i, 2 * ‖P.fH i‖ ^ 2 - 1 ≤ 1 := fun i => by
      have := hH i; nlinarith [norm_nonneg (P.fH i)]
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => this i
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  rw [hR] at hsum
  linarith

/-- **Budget form of the weighted count.** If owner costs `β ≥ 0` on `O` satisfy
`Σ_{q∈O} β_q ≤ 1`, then `4·mass − E − 2N ≤ #H + #{mixed points not certified with costs β}`.
An owner whose positive part is large has small cost. -/
theorem four_mass_sub_energy_le_add_card_fail_budget [FiniteDimensional ℝ V]
    (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ q, 1 ≤ P.mP q) (hH : ∀ i, ‖P.fH i‖ ≤ 1)
    (hMn : ∀ x, ‖P.fM x‖ ≤ 1) (own : ιM → ιP) (O : Finset ιP) (hO : ∀ x, own x ∈ O)
    (hOne : O.Nonempty) (β : ιP → ℝ) (hβ0 : ∀ q ∈ O, 0 ≤ β q) (hβ1 : ∑ q ∈ O, β q ≤ 1)
    (good : Finset ιM) (hgood : ∀ x ∈ good, P.CertifiedWith own β x) :
    4 * P.mass - P.energy - 2 * P.count ≤
      (Fintype.card ιH : ℝ) + (Finset.univ \ good).card := by
  have hcard : (0 : ℝ) < O.card := by exact_mod_cast hOne.card_pos
  set δ := (1 - ∑ q ∈ O, β q) / (O.card : ℝ) with hδ
  have hδ0 : 0 ≤ δ := div_nonneg (by linarith) hcard.le
  refine P.four_mass_sub_energy_le_add_card_fail_weighted hm₂ hmP hH hMn own O hO
    (fun q => β q + δ) (fun q hq => by linarith [hβ0 q hq]) ?_ good fun x hx n e ev hd => ?_
  · rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hδ]; field_simp; ring
  · have h1 := hgood x hx n e ev hd
    have h2 := positivePartForm_nonneg e ev (P.fM x)
    nlinarith

/-- **Failure-tolerant count.** With `r = #O` owners,
`4·mass − E − 2N ≤ #H + #{uncertified mixed points}`. -/
theorem four_mass_sub_energy_le_add_card_fail [FiniteDimensional ℝ V] (hm₂ : ∀ i, 2 ≤ P.m₂ i)
    (hmP : ∀ q, 1 ≤ P.mP q) (hH : ∀ i, ‖P.fH i‖ ≤ 1) (hMn : ∀ x, ‖P.fM x‖ ≤ 1)
    (own : ιM → ιP) (O : Finset ιP) (hO : ∀ x, own x ∈ O) (hOne : O.Nonempty)
    (good : Finset ιM) (hgood : ∀ x ∈ good, P.Certified own O.card x) :
    4 * P.mass - P.energy - 2 * P.count ≤
      (Fintype.card ιH : ℝ) + (Finset.univ \ good).card := by
  have hcard : (0 : ℝ) < O.card := by exact_mod_cast hOne.card_pos
  refine P.four_mass_sub_energy_le_add_card_fail_weighted hm₂ hmP hH hMn own O hO
    (fun _ => 1 / (O.card : ℝ)) (fun _ _ => by positivity) ?_ good fun x hx n e ev hd => ?_
  · rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  · have := hgood x hx n e ev hd
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hcard]
    linarith

omit [Fintype ι₂] [Fintype ιH] [Fintype ιM] [DecidableEq ιM] in
/-- **Hybrid certificate for the owner form.** -/
theorem positivePartForm_owner_ge_of_hybrid [FiniteDimensional ℝ V] (hmP : ∀ q, 1 ≤ P.mP q)
    (p : ιP) (Lset : Finset ιP) {n : ℕ} (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ)
    (hd : ∀ v, P.ownerForm p v = ∑ j, ev j * ⟪e j, v⟫ ^ 2)
    {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ d ∈ Submodule.span ℝ (Set.range fun q : {q // q ∈ Lset} => P.h q),
      |⟪d, P.g p⟫| ≤ κ * ‖d‖)
    {σ2 lam0 : ℝ}
    (hσ : ∑ q : {q // q ∉ Lset}, 2 * P.mP q * (|⟪P.h q, P.g p⟫| + ‖P.h q‖ * κ) ^ 2 ≤ σ2)
    (hgap : κ ^ 2 < ‖P.g p‖ ^ 2) (hlam0 : 0 < lam0)
    (hlam0le : lam0 ≤ 2 * P.mP p * (‖P.g p‖ ^ 2 - κ ^ 2) - σ2 / (‖P.g p‖ ^ 2 - κ ^ 2))
    (f : V) :
    2 * P.mP p * max (|⟪P.g p, f⟫| - (κ + Real.sqrt (σ2 / (4 * lam0))) * ‖f‖) 0 ^ 2 ≤
      positivePartForm e ev f := by
  classical
  refine positivePartForm_ge_of_hybridInterference e ev (by linarith [hmP p]) (P.g p)
    (fun q : {q // q ∈ Lset} => 2 * P.mP q) (fun q => by linarith [hmP q.1])
    (fun q => P.h q) (fun q : {q // q ∉ Lset} => 2 * P.mP q) (fun q => by linarith [hmP q.1])
    (fun q => P.h q) (fun v => ?_) hκ0 hκ hσ hgap hlam0 hlam0le f
  rw [← hd, ownerForm]
  have hsplit : ∑ q : {q // q ∈ Lset}, 2 * P.mP q * ⟪P.h q, v⟫ ^ 2 +
      ∑ q : {q // q ∉ Lset}, 2 * P.mP q * ⟪P.h q, v⟫ ^ 2 =
      ∑ q, 2 * P.mP q * ⟪P.h q, v⟫ ^ 2 := by
    convert Fintype.sum_subtype_add_sum_subtype (fun q => q ∈ Lset)
      (fun q => 2 * P.mP q * ⟪P.h q, v⟫ ^ 2)
  rw [← hsplit]
  ring

/-- **Hybrid failure count.** Fix owner weights `w ≥ 0` on `O` with `Σ_{q∈O} w_q = 1`. For each
mixed point `x`, choose a large set `L_x`, an angle `κ_x`, a small-overlap bound `σ²_x`, an
eigenvalue floor `λ₀_x` and a slack `θ_x > 0` with
`‖f_x‖² − ½ ≤ w_{own x}·2m((|⟪g, f_x⟫| − θ_x‖f_x‖)⁺)²`. With `K_x = κ_x + √(σ²_x/(4λ₀_x))`,
`4·mass − E − 2N ≤ #H + Σ_x (K_x/θ_x)²`. -/
theorem four_mass_sub_energy_le_add_hybrid_count [FiniteDimensional ℝ V]
    (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ q, 1 ≤ P.mP q) (hH : ∀ i, ‖P.fH i‖ ≤ 1)
    (hMn : ∀ x, ‖P.fM x‖ ≤ 1) (own : ιM → ιP) (O : Finset ιP) (hO : ∀ x, own x ∈ O)
    (w : ιP → ℝ) (hw0 : ∀ q ∈ O, 0 ≤ w q) (hw1 : ∑ q ∈ O, w q = 1)
    (Lset : ιM → Finset ιP) (κ σ2 lam0 θ : ιM → ℝ)
    (hκ0 : ∀ x, 0 ≤ κ x)
    (hκ : ∀ x, ∀ d ∈ Submodule.span ℝ (Set.range fun q : {q // q ∈ Lset x} => P.h q),
      |⟪d, P.g (own x)⟫| ≤ κ x * ‖d‖)
    (hσ : ∀ x, ∑ q : {q // q ∉ Lset x},
      2 * P.mP q * (|⟪P.h q, P.g (own x)⟫| + ‖P.h q‖ * κ x) ^ 2 ≤ σ2 x)
    (hgap : ∀ x, κ x ^ 2 < ‖P.g (own x)‖ ^ 2) (hlam0 : ∀ x, 0 < lam0 x)
    (hlam0le : ∀ x, lam0 x ≤ 2 * P.mP (own x) * (‖P.g (own x)‖ ^ 2 - κ x ^ 2) -
      σ2 x / (‖P.g (own x)‖ ^ 2 - κ x ^ 2))
    (hθ : ∀ x, 0 < θ x)
    (hθdef : ∀ x, ‖P.fM x‖ ^ 2 - 1 / 2 ≤ w (own x) *
      (2 * P.mP (own x) * max (|⟪P.g (own x), P.fM x⟫| - θ x * ‖P.fM x‖) 0 ^ 2)) :
    4 * P.mass - P.energy - 2 * P.count ≤ (Fintype.card ιH : ℝ) +
      ∑ x, ((κ x + Real.sqrt (σ2 x / (4 * lam0 x))) / θ x) ^ 2 := by
  classical
  set K : ιM → ℝ := fun x => κ x + Real.sqrt (σ2 x / (4 * lam0 x)) with hK
  set good := Finset.univ.filter fun x => K x ≤ θ x with hgood
  have hcert : ∀ x ∈ good, P.CertifiedWith own w x := by
    intro x hx n e ev hd
    have hKx : K x ≤ θ x := (Finset.mem_filter.mp hx).2
    have hfloor := P.positivePartForm_owner_ge_of_hybrid hmP (own x) (Lset x) e ev hd
      (hκ0 x) (hκ x) (hσ x) (hgap x) (hlam0 x) (hlam0le x) (P.fM x)
    refine (hθdef x).trans (mul_le_mul_of_nonneg_left (le_trans ?_ hfloor) (hw0 _ (hO x)))
    have hm : 0 ≤ 2 * P.mP (own x) := by linarith [hmP (own x)]
    refine mul_le_mul_of_nonneg_left ?_ hm
    refine pow_le_pow_left₀ (le_max_right _ _) (max_le_max ?_ le_rfl) 2
    have := mul_le_mul_of_nonneg_right hKx (norm_nonneg (P.fM x))
    simp only [hK] at this
    linarith
  have hmain := P.four_mass_sub_energy_le_add_card_fail_weighted hm₂ hmP hH hMn own O hO w hw0
    hw1 good hcert
  have hbad : ((Finset.univ \ good).card : ℝ) ≤ ∑ x, (K x / θ x) ^ 2 := by
    have e : Finset.univ \ good = Finset.univ.filter fun x => θ x < K x := by
      ext x; simp [hgood, not_le]
    rw [e]
    exact card_filter_lt_le_sum_sq_div Finset.univ K θ fun x _ => hθ x
  linarith

end HorizontalPacket

end GaloisForLFunctions.HilbertMetric
