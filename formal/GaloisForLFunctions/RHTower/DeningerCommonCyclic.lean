import GaloisForLFunctions.RHTower.DeningerCentralizerRotate
import GaloisForLFunctions.RHTower.DeningerCycLenBound

/-!
# Commuting elements lie in a common cyclic subgroup

An element commuting with a cyclically reduced word of at least two letters is the element realizing
a rotation of that word times a power of it.  If the rotation is trivial or full the realizing
element is a base element, which commutes with the word only if it is trivial.  Otherwise the
realizing element is shorter than the word, and the roles may be exchanged: the word commutes with
it, so cyclically reducing it and applying the same statement to the shorter word expresses both in
a common cyclic subgroup.  The descent is the Euclidean algorithm on the lengths.

The two structural hypotheses are discharged in a root adjunction, where the centralizer of a
nontrivial base element and of an element of a factor consists of elements of length at most one.

* `deningerCommon_cyclic` : the descent.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Commuting elements lie in a common cyclic subgroup.**  If a base element commuting with a
cyclically reduced word of at least two letters is trivial, and no conjugate of an element of a
factor commutes with such a word, then an element commuting with such a word and the word itself are
powers of one element. -/
theorem deningerCommon_cyclic
    (hbase : ∀ (k : H) (V : List (Σ i, G i)), 2 ≤ V.length →
      (∀ p ∈ V, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V →
      (∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) →
      PushoutI.base φ k * deningerLetterProd (φ := φ) V =
        deningerLetterProd (φ := φ) V * PushoutI.base φ k → PushoutI.base φ k = 1)
    (hshort : ∀ (V : List (Σ i, G i)), 2 ≤ V.length →
      (∀ p ∈ V, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V →
      (∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) →
      ∀ (i : ι) (x : G i) (g : PushoutI φ), x ∉ (φ i).range →
        g * PushoutI.of (φ := φ) i x * g⁻¹ * deningerLetterProd (φ := φ) V =
          deningerLetterProd (φ := φ) V * (g * PushoutI.of (φ := φ) i x * g⁻¹) → False)
    (X : List (Σ i, G i)) (hX2 : 2 ≤ X.length)
    (hXred : ∀ p ∈ X, p.2 ∉ (φ p.1).range)
    (hXalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) X)
    (hXcyc : ∀ p ∈ X.getLast?, ∀ q ∈ X.head?, p.1 ≠ q.1)
    (z : PushoutI φ)
    (hz : z⁻¹ * deningerLetterProd (φ := φ) X * z = deningerLetterProd (φ := φ) X) :
    ∃ (v : PushoutI φ) (n : ℕ), 0 < n ∧ v ^ n = deningerLetterProd (φ := φ) X ∧
      z ∈ Subgroup.zpowers v := by
  classical
  suffices Hn : ∀ N : ℕ, ∀ X : List (Σ i, G i), X.length ≤ N → 2 ≤ X.length →
      (∀ p ∈ X, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) X →
      (∀ p ∈ X.getLast?, ∀ q ∈ X.head?, p.1 ≠ q.1) →
      ∀ z : PushoutI φ,
        z⁻¹ * deningerLetterProd (φ := φ) X * z = deningerLetterProd (φ := φ) X →
        ∃ (v : PushoutI φ) (n : ℕ), 0 < n ∧ v ^ n = deningerLetterProd (φ := φ) X ∧
          z ∈ Subgroup.zpowers v from
    Hn X.length X le_rfl hX2 hXred hXalt hXcyc z hz
  clear hz z hXcyc hXalt hXred hX2 X
  intro N
  induction N with
  | zero =>
    intro X hlen h2 _ _ _ _ _
    omega
  | succ N ih =>
    intro X hlen h2 hred halt hcyc z hz
    obtain ⟨t, m, j, ht, -, htr⟩ := deningerCent_rotate (d := d) X h2 hred halt hcyc z hz
    have hb : deningerRotateCentElt φ X t m = deningerLetterProd (φ := φ) X ^ j * z :=
      mul_inv_eq_iff_eq_mul.mp htr
    have hzcomm : deningerLetterProd (φ := φ) X * z = z * deningerLetterProd (φ := φ) X := by
      have h := congrArg (fun y : PushoutI φ => z * y) hz
      simp only [← mul_assoc, mul_inv_cancel, one_mul] at h
      exact h
    have hbcomm : deningerRotateCentElt φ X t m * deningerLetterProd (φ := φ) X =
        deningerLetterProd (φ := φ) X * deningerRotateCentElt φ X t m := by
      rw [hb, mul_assoc, ← hzcomm, ← mul_assoc, ← mul_assoc]
      congr 1
      rw [← zpow_add_one, ← zpow_one_add, add_comm]
    have hwne : deningerLetterProd (φ := φ) X ≠ 1 := by
      intro hc
      have h1 : deningerLen d (deningerLetterProd (φ := φ) X) = X.length :=
        deningerLen_letterProd (d := d) X hred halt
      rw [hc, deningerLen_one] at h1
      omega
    have hinvcomm : ∀ a c : PushoutI φ, a⁻¹ * c = c * a⁻¹ → a * c = c * a := by
      intro a c h
      calc a * c = a * (c * a⁻¹) * a := by group
        _ = a * (a⁻¹ * c) * a := by rw [h]
        _ = c * a := by group
    have hsolve : ∀ (c : PushoutI φ) (e : ℤ), c = deningerLetterProd (φ := φ) X ^ e * z →
        deningerLetterProd (φ := φ) X ^ (-e) * c = z := by
      intro c e h
      rw [h, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · -- the rotation is trivial: the realizing element is a base element
      have hb0 : deningerRotateCentElt φ X 0 m = (PushoutI.base φ m)⁻¹ := by
        rw [deningerRotateCentElt, List.take_zero, deningerLetterProd_nil, one_mul]
      rw [hb0] at hbcomm
      have hmcomm : PushoutI.base φ m * deningerLetterProd (φ := φ) X =
          deningerLetterProd (φ := φ) X * PushoutI.base φ m :=
        hinvcomm _ _ hbcomm
      have hm1 : PushoutI.base φ m = 1 := hbase m X h2 hred halt hcyc hmcomm
      refine ⟨deningerLetterProd (φ := φ) X, 1, Nat.one_pos, pow_one _, -j, ?_⟩
      show deningerLetterProd (φ := φ) X ^ (-j) = z
      have hone : (1 : PushoutI φ) = deningerLetterProd (φ := φ) X ^ j * z := by
        rw [← hb, hb0, hm1, inv_one]
      rw [← hsolve 1 j hone, mul_one]
    rcases eq_or_lt_of_le ht with hteq | htlt
    · -- the rotation is full: the realizing element is the word times a base element
      have hbL : deningerRotateCentElt φ X t m =
          deningerLetterProd (φ := φ) X * (PushoutI.base φ m)⁻¹ := by
        rw [deningerRotateCentElt, hteq, List.take_length]
      rw [hbL] at hbcomm
      have h1 : (PushoutI.base φ m)⁻¹ * deningerLetterProd (φ := φ) X =
          deningerLetterProd (φ := φ) X * (PushoutI.base φ m)⁻¹ := by
        refine mul_left_cancel (a := deningerLetterProd (φ := φ) X) ?_
        calc deningerLetterProd (φ := φ) X *
              ((PushoutI.base φ m)⁻¹ * deningerLetterProd (φ := φ) X)
            = deningerLetterProd (φ := φ) X * (PushoutI.base φ m)⁻¹ *
              deningerLetterProd (φ := φ) X := by group
          _ = deningerLetterProd (φ := φ) X *
              (deningerLetterProd (φ := φ) X * (PushoutI.base φ m)⁻¹) := hbcomm
      have hmcomm : PushoutI.base φ m * deningerLetterProd (φ := φ) X =
          deningerLetterProd (φ := φ) X * PushoutI.base φ m := hinvcomm _ _ h1
      have hm1 : PushoutI.base φ m = 1 := hbase m X h2 hred halt hcyc hmcomm
      refine ⟨deningerLetterProd (φ := φ) X, 1, Nat.one_pos, pow_one _, -j + 1, ?_⟩
      show deningerLetterProd (φ := φ) X ^ (-j + 1) = z
      have hbw : deningerLetterProd (φ := φ) X = deningerLetterProd (φ := φ) X ^ j * z := by
        rw [← hb, hbL, hm1, inv_one, mul_one]
      rw [zpow_add, zpow_one, ← hsolve _ j hbw]
    · -- the rotation is proper: the realizing element is shorter, and the roles exchange
      have hPne : X.take t ≠ [] := by
        intro hc
        have h0 : (X.take t).length = 0 := by rw [hc]; rfl
        rw [List.length_take, min_eq_left ht] at h0
        omega
      obtain ⟨M, p, hMp⟩ : ∃ M p, X.take t = M ++ [p] := by
        obtain ⟨w, hw⟩ : ∃ w, (X.take t).getLast? = some w := by
          cases hg : (X.take t).getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 hg) hPne
          | some w => exact ⟨w, rfl⟩
        exact ⟨(X.take t).dropLast, w, (List.dropLast_append_getLast? _ hw).symm⟩
      have hPred : ∀ q ∈ X.take t, q.2 ∉ (φ q.1).range := fun q hq =>
        hred q (List.take_subset t X hq)
      have hPalt : List.IsChain (fun q r : Σ i, G i => q.1 ≠ r.1) (X.take t) := halt.take t
      set P : List (Σ i, G i) := M ++ [(⟨p.1, p.2 * φ p.1 m⁻¹⟩ : Σ i, G i)] with hP
      have hPprod : deningerLetterProd (φ := φ) P = deningerRotateCentElt φ X t m := by
        rw [hP, ← deningerLetterProd_mul_base_snoc, ← hMp, deningerRotateCentElt, map_inv]
      have hPred' : ∀ q ∈ P, q.2 ∉ (φ q.1).range :=
        deningerAbsorbRight_reduced M p m⁻¹ (by rw [← hMp]; exact hPred)
      have hPfst : P.map Sigma.fst = (X.take t).map Sigma.fst := by
        rw [hP, hMp, deningerAbsorbRight_map_fst]
      have hPalt' : List.IsChain (fun q r : Σ i, G i => q.1 ≠ r.1) P :=
        deningerIsChain_of_map_fst (X.take t) P hPfst hPalt
      have hPne' : P ≠ [] := by
        rw [hP]
        exact List.append_ne_nil_of_right_ne_nil M (by simp)
      have hPlen : P.length = t := by
        have h1 : P.length = (X.take t).length := by
          have := congrArg List.length hPfst
          simpa using this
        rw [h1, List.length_take, min_eq_left ht]
      obtain ⟨C, R, V, hsplit, hRne, hVne, hVred, hValt, -, hprodR, hVcases, hVlen⟩ :=
        deningerExists_cycData_len (φ := φ) P hPne' hPred' hPalt'
      have hbconj : deningerRotateCentElt φ X t m =
          deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) V *
            (deningerLetterProd (φ := φ) C)⁻¹ := by
        rw [← hPprod, hP, ← hP, hsplit, deningerLetterProd_append, hprodR, ← mul_assoc]
      have hVsmall : V.length ≤ N := by
        have h1 : C.length + R.length = P.length := by
          rw [hsplit] at hPlen ⊢
          simp
        omega
      set y : PushoutI φ := (deningerLetterProd (φ := φ) C)⁻¹ * deningerLetterProd (φ := φ) X *
        deningerLetterProd (φ := φ) C with hy
      have hVcomm : y * deningerLetterProd (φ := φ) V =
          deningerLetterProd (φ := φ) V * y := by
        have h1 := hbcomm
        rw [hbconj] at h1
        rw [hy]
        calc (deningerLetterProd (φ := φ) C)⁻¹ * deningerLetterProd (φ := φ) X *
              deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) V
            = (deningerLetterProd (φ := φ) C)⁻¹ *
              (deningerLetterProd (φ := φ) X *
                (deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) V *
                  (deningerLetterProd (φ := φ) C)⁻¹)) * deningerLetterProd (φ := φ) C := by group
          _ = (deningerLetterProd (φ := φ) C)⁻¹ *
              (deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) V *
                (deningerLetterProd (φ := φ) C)⁻¹ * deningerLetterProd (φ := φ) X) *
              deningerLetterProd (φ := φ) C := by rw [← h1]
          _ = deningerLetterProd (φ := φ) V *
              ((deningerLetterProd (φ := φ) C)⁻¹ * deningerLetterProd (φ := φ) X *
                deningerLetterProd (φ := φ) C) := by group
      have hVconj : y⁻¹ * deningerLetterProd (φ := φ) V * y = deningerLetterProd (φ := φ) V := by
        calc y⁻¹ * deningerLetterProd (φ := φ) V * y
            = y⁻¹ * (deningerLetterProd (φ := φ) V * y) := by group
          _ = y⁻¹ * (y * deningerLetterProd (φ := φ) V) := by rw [← hVcomm]
          _ = deningerLetterProd (φ := φ) V := by group
      by_cases hV2 : 2 ≤ V.length
      · have hVcyc : ∀ q ∈ V.getLast?, ∀ r ∈ V.head?, q.1 ≠ r.1 := by
          rcases hVcases with hc | hc
          · omega
          · exact hc
        obtain ⟨v₀, n₀, hn₀, hv₀, hmem⟩ := ih V hVsmall hV2 hVred hValt hVcyc y hVconj
        obtain ⟨k, hk'⟩ := hmem
        have hk : v₀ ^ k = y := hk'
        set v : PushoutI φ := deningerLetterProd (φ := φ) C * v₀ *
          (deningerLetterProd (φ := φ) C)⁻¹ with hv
        have hvk : v ^ k = deningerLetterProd (φ := φ) X := by
          rw [hv, conj_zpow, hk, hy]
          group
        have hvn₀ : v ^ n₀ = deningerRotateCentElt φ X t m := by
          rw [hv, hbconj, ← hv₀]
          exact_mod_cast conj_zpow (i := (n₀ : ℤ)) (a := deningerLetterProd (φ := φ) C) (b := v₀)
        have hk0 : k ≠ 0 := by
          intro hc
          rw [hc, zpow_zero] at hvk
          exact hwne hvk.symm
        have hzmem : z ∈ Subgroup.zpowers v := by
          have hzv : z = v ^ (-(j * k) + n₀) := by
            rw [zpow_add, zpow_neg, zpow_mul', hvk]
            rw [show (v ^ (n₀ : ℤ)) = deningerRotateCentElt φ X t m by
              rw [zpow_natCast]; exact hvn₀]
            rw [hb]
            group
          exact ⟨-(j * k) + n₀, hzv.symm⟩
        rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
        · refine ⟨v⁻¹, (-k).toNat, by omega, ?_, ?_⟩
          · have h1 : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
            calc (v⁻¹) ^ (-k).toNat = (v⁻¹) ^ (((-k).toNat : ℤ)) := (zpow_natCast _ _).symm
              _ = (v⁻¹) ^ (-k) := by rw [h1]
              _ = v ^ k := by rw [inv_zpow', neg_neg]
              _ = deningerLetterProd (φ := φ) X := hvk
          · rwa [Subgroup.zpowers_inv]
        · refine ⟨v, k.toNat, by omega, ?_, hzmem⟩
          rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
          exact hvk
      · -- the cyclic reduction is a single letter, which is excluded
        exfalso
        have hVpos : 0 < V.length := List.length_pos_iff.2 hVne
        obtain ⟨q, hq⟩ : ∃ q, V = [q] := List.length_eq_one_iff.mp (by omega)
        refine hshort X h2 hred halt hcyc q.1 q.2 (deningerLetterProd (φ := φ) C)
          (hVred q (by rw [hq]; exact List.mem_cons_self)) ?_
        have hVq : deningerLetterProd (φ := φ) V = PushoutI.of (φ := φ) q.1 q.2 := by
          rw [hq, deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
        rw [← hVq]
        have h1 := hbcomm
        rw [hbconj] at h1
        exact h1

end RHTower
