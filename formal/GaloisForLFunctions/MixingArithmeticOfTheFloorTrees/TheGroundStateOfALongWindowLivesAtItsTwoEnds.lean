import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBindingEnergyOfAWindowIsCarriedByItsFloorTrees

/-!
# The ground state of a long window lives at its two ends

Split the floor maps of the window `(R, R + J]` at a threshold `K`. A **long** floor map,
`k ≥ K`, joins a parent block `a` with `K a < R + J` to a child block `b ≥ KR`: its edges run
from the **bottom** of the window to its **top**. The weighted Schur test then bounds its contact
form by `√k (bot/s + s·top)` for every `s > 0` (`sum_longMap_le`), where `bot` and `top` are the
masses of the packet on the bottom and on the top. The short floor maps, `k < K`, are bounded by
`2√k` times the whole mass (`sum_floorMap_le`).

With the archimedean floor `A(0)` of the neutral part without floor trees, the eigenvalue
`λ = −μ` of an eigenvector `φ` satisfies (`binding_le_short_add_long`)

  `(μ + A(0) − 2 S_short) Σ φ² ≤ S_long (bot(φ)/s + s·top(φ))`,

with `S_short = Σ_{k < K} Λ(k)/√k` and `S_long = Σ_{K ≤ k ≤ Q} Λ(k)/√k`; optimizing `s`
(`sq_binding_excess_le`),

  `(μ + A(0) − 2 S_short)² (Σ φ²)² ≤ 4 S_long² · bot(φ) · top(φ)`.

The binding energy of a window of ratio `ρ` is of order `√ρ`, the short sum of order `√K`, the
long sum of order `√ρ`. So for `K = ρ/M` with a large fixed `M` the left side is a fixed fraction
of `ρ (Σ φ²)²`, and the ground state carries a fixed fraction of its mass both within the factor
`M` of the bottom and within the factor `M` of the top of the window: the binding beyond what the
short trees can give is carried by the long trees, which only join the two ends.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-- The mass of a packet on the bottom of the window: the blocks `a` with `K a < R + J`. -/
def bottomMass (K R J : ℕ) (σ : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range J, if K * (R + j) < R + J then σ j ^ 2 else 0

/-- The mass of a packet on the top of the window: the blocks `b ≥ KR`. -/
def topMass (K R J : ℕ) (σ : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range J, if K * R ≤ R + j then σ j ^ 2 else 0

/-- **A long floor map joins the bottom to the top.** For `k ≥ K` its contact form is at most
`√k (bot/s + s·top)` for every `s > 0`: weighted Schur test with weight `√k s` on the edges. -/
theorem sum_longMap_le {R J K k : ℕ} (hR : 1 ≤ R) (hk : 2 ≤ k) (hKk : K ≤ k) (σ : ℕ → ℝ)
    {s : ℝ} (hs : 0 < s) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
        (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0) ≤
      Real.sqrt k * (bottomMass K R J σ / s + s * topMass K R J σ) := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
  obtain ⟨t, htdef⟩ : ∃ t, t = Real.sqrt k * s := ⟨_, rfl⟩
  have ht : 0 < t := htdef ▸ mul_pos hsk hs
  set P : ℕ → ℕ → ℝ := fun j l => if (R + l) / k = R + j then 1 else 0 with hP
  -- the symmetric indicator is the parent–child indicator in both orders
  have hsplit : ∀ j l, (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0) =
      P j l + P l j := by
    intro j l
    simp only [hP]
    rcases lt_trichotomy j l with hjl | hjl | hjl
    · rw [max_eq_right (by omega), min_eq_left (by omega)]
      have : ¬ (R + j) / k = R + l := fun h => by
        have h' := Nat.div_le_self (R + j) k
        rw [h] at h'
        omega
      rw [if_neg this, add_zero]
    · subst hjl
      have : ¬ (R + j) / k = R + j := fun h => by
        have h' := Nat.div_lt_self (show 0 < R + j by omega) (show 1 < k by omega)
        rw [h] at h'
        exact lt_irrefl _ h'
      rw [max_self, min_self, if_neg this, add_zero]
    · rw [max_eq_left (by omega), min_eq_right (by omega)]
      have : ¬ (R + l) / k = R + j := fun h => by
        have h' := Nat.div_le_self (R + l) k
        rw [h] at h'
        omega
      rw [if_neg this, zero_add]
  have hswap : ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * P l j =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * P j l := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have hsum : ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
      (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0) =
      2 * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * P j l := by
    simp only [hsplit, mul_add, Finset.sum_add_distrib, hswap]
    ring
  -- a parent `R + j` of a child `R + l` of the window lies in the bottom, the child in the top
  have hbot : ∀ j l, l < J → (R + l) / k = R + j → K * (R + j) < R + J := fun j l hl hd => by
    have h1 : (R + l) / k * k ≤ R + l := Nat.div_mul_le_self _ _
    rw [hd] at h1
    calc K * (R + j) ≤ k * (R + j) := Nat.mul_le_mul hKk le_rfl
      _ = (R + j) * k := mul_comm _ _
      _ ≤ R + l := h1
      _ < R + J := by omega
  have htop : ∀ j l, (R + l) / k = R + j → K * R ≤ R + l := fun j l hd => by
    have h1 : (R + l) / k * k ≤ R + l := Nat.div_mul_le_self _ _
    rw [hd] at h1
    calc K * R ≤ k * (R + j) := Nat.mul_le_mul hKk (by omega)
      _ = (R + j) * k := mul_comm _ _
      _ ≤ R + l := h1
  have hpair : ∀ j ∈ range J, ∀ l ∈ range J, 2 * (σ j * σ l * P j l) ≤
      P j l * ((if K * (R + j) < R + J then σ j ^ 2 else 0) / t) +
        P j l * (t * (if K * R ≤ R + l then σ l ^ 2 else 0)) := by
    intro j _ l hl
    by_cases hd : (R + l) / k = R + j
    · have h1 : P j l = 1 := by simp only [hP, if_pos hd]
      rw [if_pos (hbot j l (Finset.mem_range.mp hl) hd), if_pos (htop j l hd), h1]
      have e : σ j ^ 2 / t + t * σ l ^ 2 - 2 * (σ j * σ l) = (σ j - t * σ l) ^ 2 / t := by
        field_simp
        ring
      have : 0 ≤ (σ j - t * σ l) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
      linarith
    · have h0 : P j l = 0 := by simp only [hP, if_neg hd]
      rw [h0]
      simp
  have hchildren : ∑ j ∈ range J, ∑ l ∈ range J,
      P j l * ((if K * (R + j) < R + J then σ j ^ 2 else 0) / t) ≤
      k * (bottomMass K R J σ / t) := by
    unfold bottomMass
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_mul]
    have := sum_children_le R k J j (by omega)
    have hnn : 0 ≤ (if K * (R + j) < R + J then σ j ^ 2 else 0) / t :=
      div_nonneg (by split_ifs <;> positivity) ht.le
    exact mul_le_mul_of_nonneg_right this hnn
  have hparents : ∑ j ∈ range J, ∑ l ∈ range J,
      P j l * (t * (if K * R ≤ R + l then σ l ^ 2 else 0)) ≤ t * topMass K R J σ := by
    unfold topMass
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Finset.sum_mul]
    have := sum_parent_le_one R k J l
    have hnn : 0 ≤ t * (if K * R ≤ R + l then σ l ^ 2 else 0) :=
      mul_nonneg ht.le (by split_ifs <;> positivity)
    calc (∑ j ∈ range J, P j l) * (t * (if K * R ≤ R + l then σ l ^ 2 else 0)) ≤
          1 * (t * (if K * R ≤ R + l then σ l ^ 2 else 0)) := mul_le_mul_of_nonneg_right this hnn
      _ = _ := one_mul _
  have h2 : 2 * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * P j l ≤
      ∑ j ∈ range J, ∑ l ∈ range J,
        (P j l * ((if K * (R + j) < R + J then σ j ^ 2 else 0) / t) +
          P j l * (t * (if K * R ≤ R + l then σ l ^ 2 else 0))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun l hl => hpair j hj l hl
  simp only [Finset.sum_add_distrib] at h2
  rw [hsum]
  have hkt : (k : ℝ) * (bottomMass K R J σ / t) = Real.sqrt k * (bottomMass K R J σ / s) := by
    rw [htdef]
    calc (k : ℝ) * (bottomMass K R J σ / (Real.sqrt k * s)) =
          ((k : ℝ) / Real.sqrt k) * (bottomMass K R J σ / s) := by ring
      _ = Real.sqrt k * (bottomMass K R J σ / s) := by rw [Real.div_sqrt]
  have hts : t * topMass K R J σ = Real.sqrt k * (s * topMass K R J σ) := by
    rw [htdef]
    ring
  linarith

/-- **The contacts split into short and long floor maps.** For every `s > 0` the contact form
is at most `2 S_short` times the mass plus `S_long (bot/s + s·top)`. -/
theorem sum_contact_le_short_long {R : ℕ} (hR : 1 ≤ R) (Q J K : ℕ) (σ : ℕ → ℝ) {s : ℝ}
    (hs : 0 < s) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
        floorContact Q (min (R + j) (R + l)) (max (R + j) (R + l)) ≤
      2 * (∑ k ∈ Icc 2 Q, if k < K then (Λ k : ℝ) / Real.sqrt k else 0) *
          ∑ j ∈ range J, σ j ^ 2 +
        (∑ k ∈ Icc 2 Q, if K ≤ k then (Λ k : ℝ) / Real.sqrt k else 0) *
          (bottomMass K R J σ / s + s * topMass K R J σ) := by
  have hexp : ∀ j l, σ j * σ l * floorContact Q (min (R + j) (R + l)) (max (R + j) (R + l)) =
      ∑ k ∈ Icc 2 Q, (Λ k : ℝ) / k * (σ j * σ l *
        (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0)) := by
    intro j l
    simp only [floorContact, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
  have hrhs : 2 * (∑ k ∈ Icc 2 Q, if k < K then (Λ k : ℝ) / Real.sqrt k else 0) *
        ∑ j ∈ range J, σ j ^ 2 +
      (∑ k ∈ Icc 2 Q, if K ≤ k then (Λ k : ℝ) / Real.sqrt k else 0) *
        (bottomMass K R J σ / s + s * topMass K R J σ) =
      ∑ k ∈ Icc 2 Q, ((if k < K then 2 * ((Λ k : ℝ) / Real.sqrt k) * ∑ j ∈ range J, σ j ^ 2
          else 0) + (if K ≤ k then (Λ k : ℝ) / Real.sqrt k *
            (bottomMass K R J σ / s + s * topMass K R J σ) else 0)) := by
    rw [Finset.sum_add_distrib,
      Finset.mul_sum (Icc 2 Q) (fun k => if k < K then (Λ k : ℝ) / Real.sqrt k else 0) 2,
      Finset.sum_mul, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
    · exact Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
  simp only [hexp]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm, hrhs]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hw : (0 : ℝ) ≤ (Λ k : ℝ) / k := div_nonneg ArithmeticFunction.vonMangoldt_nonneg hk0.le
  have hdiv : (Λ k : ℝ) / k * Real.sqrt k = (Λ k : ℝ) / Real.sqrt k := by
    have e : Real.sqrt k / k = 1 / Real.sqrt k := Real.sqrt_div_self'
    calc (Λ k : ℝ) / k * Real.sqrt k = (Λ k : ℝ) * (Real.sqrt k / k) := by ring
      _ = (Λ k : ℝ) * (1 / Real.sqrt k) := by rw [e]
      _ = (Λ k : ℝ) / Real.sqrt k := by ring
  have hpull : ∑ j ∈ range J, ∑ l ∈ range J, (Λ k : ℝ) / k * (σ j * σ l *
      (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0)) =
      (Λ k : ℝ) / k * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
        (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  rw [hpull]
  by_cases hkK : k < K
  · rw [if_pos hkK, if_neg (show ¬ K ≤ k by omega), add_zero]
    have h := sum_floorMap_le R J k hR hk2 σ
    calc (Λ k : ℝ) / k * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
          (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0)
        ≤ (Λ k : ℝ) / k * (2 * Real.sqrt k * ∑ j ∈ range J, σ j ^ 2) :=
          mul_le_mul_of_nonneg_left h hw
      _ = 2 * ((Λ k : ℝ) / k * Real.sqrt k) * ∑ j ∈ range J, σ j ^ 2 := by ring
      _ = _ := by rw [hdiv]
  · rw [if_neg hkK, if_pos (show K ≤ k by omega), zero_add]
    have h := sum_longMap_le (J := J) hR hk2 (show K ≤ k by omega) σ hs
    calc (Λ k : ℝ) / k * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l *
          (if max (R + j) (R + l) / k = min (R + j) (R + l) then (1 : ℝ) else 0)
        ≤ (Λ k : ℝ) / k * (Real.sqrt k * (bottomMass K R J σ / s + s * topMass K R J σ)) :=
          mul_le_mul_of_nonneg_left h hw
      _ = (Λ k : ℝ) / k * Real.sqrt k * (bottomMass K R J σ / s + s * topMass K R J σ) := by
          ring
      _ = _ := by rw [hdiv]

/-- **The binding energy beyond the short floor maps is carried by the two ends.** For an
eigenvector `φ` of the window with eigenvalue `λ` and every `s > 0`,
`(−λ + A(0) − 2 S_short) Σ φ² ≤ S_long (bot(φ)/s + s·top(φ))`. -/
theorem binding_le_short_add_long {Q R J K : ℕ} (hR : 1 ≤ R) {φ : Fin J → ℝ}
    {lam : ℝ} (heig : neutralWindow Q R J *ᵥ φ = lam • φ) {s : ℝ} (hs : 0 < s) :
    (-lam + EF.gammaBracket 0 -
        2 * ∑ k ∈ Icc 2 Q, (if k < K then (Λ k : ℝ) / Real.sqrt k else 0)) *
        ∑ j ∈ range J, extendFin φ j ^ 2 ≤
      (∑ k ∈ Icc 2 Q, if K ≤ k then (Λ k : ℝ) / Real.sqrt k else 0) *
        (bottomMass K R J (extendFin φ) / s + s * topMass K R J (extendFin φ)) := by
  have h1 := sum_neutralBlock_one_ge hR J (extendFin φ)
  have h2 := sum_contact_le_short_long hR Q J K (extendFin φ) hs
  have hsplit : ∑ j ∈ range J, ∑ l ∈ range J,
      extendFin φ j * extendFin φ l * neutralBlock Q (R + j) (R + l) =
      ∑ j ∈ range J, ∑ l ∈ range J,
          extendFin φ j * extendFin φ l * neutralBlock 1 (R + j) (R + l) -
        ∑ j ∈ range J, ∑ l ∈ range J, extendFin φ j * extendFin φ l *
          floorContact Q (min (R + j) (R + l)) (max (R + j) (R + l)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [neutralBlock_eq_one_sub]; ring
  have hb : bilin (neutralWindow Q R J) φ φ =
      ∑ j ∈ range J, ∑ l ∈ range J,
        extendFin φ j * extendFin φ l * neutralBlock Q (R + j) (R + l) :=
    sum_fin_windowMatrix_eq (neutralBlock Q) R φ
  have hmass : ∑ j ∈ range J, extendFin φ j ^ 2 = ∑ k, φ k * φ k := by
    rw [show ∑ k, φ k * φ k = ∑ j ∈ range J, extendFin (fun k => φ k * φ k) j from
      sum_fin_eq_sum_range_extendFin _]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [extendFin, dif_pos (Finset.mem_range.mp hj), sq]
  have heigen : bilin (neutralWindow Q R J) φ φ = lam * ∑ j ∈ range J, extendFin φ j ^ 2 := by
    rw [bilin_eigen heig, hmass]
  rw [hb, hsplit] at heigen
  linarith

/-- Optimizing the weight in `κ m ≤ S (b/s + s t)` at `s = √(b/t)` gives `κ² m² ≤ 4 S² b t`. -/
theorem sq_le_of_le_weighted {κ m S b t : ℝ} (hκ : 0 < κ) (hm : 0 ≤ m) (hb : 0 < b)
    (ht : 0 < t) (h : κ * m ≤ S * (b / Real.sqrt (b / t) + Real.sqrt (b / t) * t)) :
    κ ^ 2 * m ^ 2 ≤ 4 * S ^ 2 * (b * t) := by
  obtain ⟨u, hu⟩ : ∃ u, Real.sqrt (b / t) = u := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [← hu]; exact Real.sqrt_pos.mpr (div_pos hb ht)
  have hsq : u ^ 2 = b / t := by rw [← hu]; exact Real.sq_sqrt (div_pos hb ht).le
  have hb' : b = u ^ 2 * t := by rw [hsq, div_mul_cancel₀ b ht.ne']
  rw [hu] at h
  have hval : b / u + u * t = 2 * (u * t) := by
    rw [hb', sq, mul_assoc, mul_div_cancel_left₀ _ hu0.ne']
    ring
  rw [hval] at h
  have := pow_le_pow_left₀ (mul_nonneg hκ.le hm) h 2
  calc κ ^ 2 * m ^ 2 = (κ * m) ^ 2 := by ring
    _ ≤ (S * (2 * (u * t))) ^ 2 := this
    _ = 4 * S ^ 2 * (u ^ 2 * t * t) := by ring
    _ = 4 * S ^ 2 * (b * t) := by rw [← hb']

/-- **The product of the masses of the ground state at the two ends is bounded below.** If the
binding energy exceeds the archimedean floor and the short floor maps,
`κ = −λ + A(0) − 2 S_short > 0`, then `κ² (Σ φ²)² ≤ 4 S_long² · bot(φ) · top(φ)`. -/
theorem sq_binding_excess_le {Q R J K : ℕ} (hR : 1 ≤ R) {φ : Fin J → ℝ}
    {lam : ℝ} (heig : neutralWindow Q R J *ᵥ φ = lam • φ)
    (hκ : 0 < -lam + EF.gammaBracket 0 -
        2 * ∑ k ∈ Icc 2 Q, (if k < K then (Λ k : ℝ) / Real.sqrt k else 0))
    (hbot : 0 < bottomMass K R J (extendFin φ)) (htop : 0 < topMass K R J (extendFin φ)) :
    (-lam + EF.gammaBracket 0 -
        2 * ∑ k ∈ Icc 2 Q, (if k < K then (Λ k : ℝ) / Real.sqrt k else 0)) ^ 2 *
        (∑ j ∈ range J, extendFin φ j ^ 2) ^ 2 ≤
      4 * (∑ k ∈ Icc 2 Q, if K ≤ k then (Λ k : ℝ) / Real.sqrt k else 0) ^ 2 *
        (bottomMass K R J (extendFin φ) * topMass K R J (extendFin φ)) :=
  sq_le_of_le_weighted hκ (Finset.sum_nonneg fun _ _ => sq_nonneg _) hbot htop
    (binding_le_short_add_long (K := K) hR heig (Real.sqrt_pos.mpr (div_pos hbot htop)))

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
