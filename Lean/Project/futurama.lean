/-
  # Futurama Theorem (Keeler's Theorem) — Formalization in Lean 4 + Mathlib
-/

import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.List
import Mathlib.Data.List.Rotate

open Equiv Equiv.Perm List

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace FuturamaTheorem

-- Keeler sequence definition
def keelerSeq (l : List α) (x y : α) : List (Perm α) :=
  match l with
  | []  => []
  | [_] => []
  | a₁ :: tail =>
    let aₖ := tail.getLastD a₁
    let middle := tail.dropLast.map (swap x)
    [swap x a₁] ++ middle ++ [swap y aₖ, swap x aₖ, swap y a₁]

/-
  Concrete examples:

  2-cycle [a, b]:
    [swap x a, swap y b, swap x b, swap y a]

  3-cycle [a, b, c]:
    [swap x a, swap x b, swap y c, swap x c, swap y a]

  4-cycle [a, b, c, d]:
    [swap x a, swap x b, swap x c, swap y d, swap x d, swap y a]
-/


-- Base case — 2-cycles
set_option maxHeartbeats 1200000 in
omit [Fintype α] in
theorem keeler_base_two (a b x y : α)
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x)
    (hby : b ≠ y) (hxy : x ≠ y) :
    (keelerSeq [a, b] x y).prod * formPerm [a, b] = swap x y := by
  unfold keelerSeq
  dsimp
  simp [List.getLastD]
  ext z
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all


-- Lemma Cycle decomposition — removing second element
-- formPerm (a :: b :: c :: tail) = formPerm (a :: c :: tail) * swap a b

set_option maxHeartbeats 1600000 in
omit [Fintype α] in
lemma formPerm_remove_second (a b c : α) (tail : List α)
    (hnd : (a :: b :: c :: tail).Nodup) :
    formPerm (a :: b :: c :: tail) = formPerm (a :: c :: tail) * swap a b := by
  have hab : a ≠ b := by simp [List.nodup_cons, List.mem_cons] at hnd; tauto
  have hac : a ≠ c := by simp [List.nodup_cons, List.mem_cons] at hnd; tauto
  have hbc : b ≠ c := by simp [List.nodup_cons, List.mem_cons] at hnd; tauto
  have ha_ct : a ∉ (c :: tail) := by
    simp only [List.nodup_cons, List.mem_cons] at hnd ⊢; tauto
  have hb_ct : b ∉ (c :: tail) := by
    simp only [List.nodup_cons, List.mem_cons] at hnd ⊢; tauto

  rw [List.formPerm_cons_cons _ _ _]
  rw [List.formPerm_cons_cons _ _ _]
  rw [List.formPerm_cons_cons _ _ _]

  -- braid relation
  have braid : swap a b * swap b c = swap a c * swap a b := by
    ext z; simp only [Perm.mul_apply, swap_apply_def]
    split_ifs <;> simp_all
  -- swap a b commutes with formPerm(c::tail)
  have comm : swap a b * formPerm (c :: tail) = formPerm (c :: tail) * swap a b := by
    ext z
    simp only [Perm.mul_apply]
    by_cases hza : z = a
    · subst hza
      simp only [swap_apply_left, List.formPerm_apply_of_notMem ha_ct,
                 List.formPerm_apply_of_notMem hb_ct]
    · by_cases hzb : z = b
      · subst hzb
        simp only [swap_apply_right, List.formPerm_apply_of_notMem hb_ct,
                   List.formPerm_apply_of_notMem ha_ct]

      · have hfa : formPerm (c :: tail) z ≠ a := by
          intro h
          have h1 : formPerm (c :: tail) a = a :=
          List.formPerm_apply_of_notMem ha_ct
          have h2 : formPerm (c :: tail) z = formPerm (c :: tail) a :=
          h.trans h1.symm
          have h3 : z = a :=
          (formPerm (c :: tail)).injective h2
          exact hza h3
        have hfb : formPerm (c :: tail) z ≠ b := by
          intro h
          have h1 : formPerm (c :: tail) b = b :=
          List.formPerm_apply_of_notMem hb_ct
          have h2 : formPerm (c :: tail) z = formPerm (c :: tail) b :=
          h.trans h1.symm
          have h3 : z = b :=
          (formPerm (c :: tail)).injective h2
          exact hzb h3

        rw [swap_apply_of_ne_of_ne hza hzb, swap_apply_of_ne_of_ne hfa hfb]

  calc swap a b * (swap b c * formPerm (c :: tail))
      = (swap a b * swap b c) * formPerm (c :: tail) := by group
    _ = (swap a c * swap a b) * formPerm (c :: tail) := by rw [braid]
    _ = swap a c * (swap a b * formPerm (c :: tail)) := by group
    _ = swap a c * (formPerm (c :: tail) * swap a b) := by rw [comm]
    _ = swap a c * formPerm (c :: tail) * swap a b := by group



-- Lemma Keeler sequence product decomposition
-- keelerSeq(a::b::c::tail) has one extra swap(x,b) compared to
-- keelerSeq(a::c::tail), inserted after swap(x,a).

omit [Fintype α] in
lemma keelerSeq_prod_remove_second (a b c : α) (tail : List α) (x y : α) :
    (keelerSeq (a :: b :: c :: tail) x y).prod =
      swap x a * swap x b * swap x a * (keelerSeq (a :: c :: tail) x y).prod := by
  unfold keelerSeq
  have hk : (b :: c :: tail).getLastD a = (c :: tail).getLastD a := by
    simp [List.getLastD]
  dsimp

  rw [hk]

  simp only [mul_assoc]
  simp


-- Keeler on single cycle

omit [Fintype α] in
set_option maxHeartbeats 1600000 in
theorem keeler_identity (l : List α) (x y : α)
    (hnd : l.Nodup) (hlen : l.length ≥ 2)
    (hx : x ∉ l) (hy : y ∉ l) (hxy : x ≠ y) :
    (keelerSeq l x y).prod * formPerm l = swap x y := by
  match l with
  | [] => simp at hlen
  | [_] => simp at hlen
  | [a, b] =>
    have hab : a ≠ b := by simp [List.nodup_cons] at hnd; exact hnd
    have hax : a ≠ x := by intro h; subst h; apply hx; simp
    have hay : a ≠ y := by intro h; subst h; apply hy; simp
    have hbx : b ≠ x := by intro h; subst h; apply hx; simp
    have hby : b ≠ y := by intro h; subst h; apply hy; simp
    exact keeler_base_two a b x y hab hax hay hbx hby hxy
  | a :: b :: c :: tail =>
    -- Extract distinctness hypotheses
    have hab : a ≠ b := by
      intro h; subst h; simp [List.nodup_cons] at hnd
    have hax : a ≠ x := by intro h; subst h; apply hx; simp
    have hay : a ≠ y := by intro h; subst h; apply hy; simp
    have hbx : b ≠ x := by intro h; subst h; apply hx; simp
    have hby : b ≠ y := by intro h; subst h; apply hy; simp
    -- Nodup for shorter list (a :: c :: tail)
    have hnd_short : (a :: c :: tail).Nodup := by
      simp only [List.nodup_cons, List.mem_cons] at hnd ⊢; tauto
    -- Length of shorter list
    have hlen_short : (a :: c :: tail).length ≥ 2 := by simp
    -- Freshness for shorter list
    have hx_short : x ∉ (a :: c :: tail) := by
      simp only [List.mem_cons] at hx ⊢; tauto
    have hy_short : y ∉ (a :: c :: tail) := by
      simp only [List.mem_cons] at hy ⊢; tauto
    -- Inductive hypothesis

    have ih := keeler_identity (a :: c :: tail) x y
                 hnd_short hlen_short hx_short hy_short hxy

    -- Decompose formPerm(long) = formPerm(short) * swap a b
    rw [formPerm_remove_second a b c tail hnd]
    -- Decompose keelerSeq(long).prod
    rw [keelerSeq_prod_remove_second a b c tail x y]

    have reassoc :
      swap x a * swap x b * swap x a * (keelerSeq (a :: c :: tail) x y).prod *
      (formPerm (a :: c :: tail) * swap a b) =
      swap x a * swap x b * swap x a *
      ((keelerSeq (a :: c :: tail) x y).prod * formPerm (a :: c :: tail)) *
      swap a b := by group

    rw [reassoc, ih]

    ext z
    simp only [Perm.mul_apply, swap_apply_def]
    split_ifs <;> simp_all


-- Properties of the Keeler sequence

omit [DecidableEq α] [Fintype α] in
-- getLastD of a nonempty list is a member of that list.
private lemma getLastD_cons_mem (d a : α) (l : List α) :
    (a :: l).getLastD d ∈ a :: l := by
  simp [List.getLastD]


omit [Fintype α] in
-- Every transposition involves exactly one of x, y paired with a cycle element.
theorem keelerSeq_uses_auxiliary (l : List α) (x y : α)
    (hlen : l.length ≥ 2) :
    ∀ t ∈ keelerSeq l x y,
      (∃ a ∈ l, t = swap x a) ∨ (∃ a ∈ l, t = swap y a) := by
  match l, hlen with
  | a₁ :: a₂ :: tail, _ =>
    intro t ht
    unfold keelerSeq at ht; dsimp at ht
    have ha₁_mem : a₁ ∈ a₁ :: a₂ :: tail := by simp

    have haₖ_mem : (a₂ :: tail).getLastD a₁ ∈ a₁ :: a₂ :: tail :=
      by simp [List.getLastD]

    simp only [List.mem_append, List.mem_cons,
               List.mem_map, List.mem_nil_iff, or_false] at ht

    rcases ht with rfl | ⟨a, ha, rfl⟩ | rfl | rfl | rfl
    · left; exact ⟨a₁, ha₁_mem, rfl⟩
    · left; exact ⟨a, List.mem_cons_of_mem _ (List.dropLast_subset _ ha), rfl⟩
    · right; exact ⟨_, haₖ_mem, rfl⟩
    · left; exact ⟨_, haₖ_mem, rfl⟩
    · right; exact ⟨a₁, ha₁_mem, rfl⟩

omit [Fintype α] in
-- swap x is injective: swap x a = swap x b → a = b
private lemma swap_right_injective (x : α) :
    Function.Injective (swap x) := by
  intro a b h
  have : swap x a x = swap x b x := by rw [h]
  simp [swap_apply_left] at this
  exact this

omit [Fintype α] in
private lemma swap_ne_swap_xy (x y a b : α) (hxy : x ≠ y) (hay : a ≠ y) (hax : a ≠ x) :
    swap x a ≠ swap y b := by
  intro h
  have : swap x a a = swap y b a := by rw [h]
  rw [swap_apply_right] at this
  -- this : x = swap y b a
  by_cases hab : a = b
  · subst hab; rw [swap_apply_right] at this; exact hxy this
  · rw [swap_apply_of_ne_of_ne hay hab] at this; exact hax this.symm


omit [Fintype α] in
-- All transpositions in the Keeler sequence are distinct.
theorem keelerSeq_nodup (l : List α) (x y : α)
    (hnd : l.Nodup) (hlen : l.length ≥ 2)
    (hx : x ∉ l) (hy : y ∉ l) (hxy : x ≠ y) :
    (keelerSeq l x y).Nodup := by
  match l with
  | [] => simp at hlen
  | [_] => simp at hlen
  | [a, b] =>
      have hab : a ≠ b := by simp [List.nodup_cons] at hnd; exact hnd
      have hax : a ≠ x := by intro h; subst h; apply hx; simp
      have hay : a ≠ y := by intro h; subst h; apply hy; simp
      have hbx : b ≠ x := by intro h; subst h; apply hx; simp
      have hby : b ≠ y := by intro h; subst h; apply hy; simp
      unfold keelerSeq; dsimp
      simp only [List.getLastD,
                List.nodup_cons, List.mem_cons, or_false, not_or, List.not_mem_nil,
                not_false_eq_true, List.nodup_nil, and_true]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · exact swap_ne_swap_xy x y a b hxy hay hax
      · intro h; exact hab (swap_right_injective x h)
      · exact swap_ne_swap_xy x y a a hxy hay hax
      · exact swap_ne_swap_xy y x b b (Ne.symm hxy) hbx hby
      · intro h; exact hab.symm (swap_right_injective y h)
      · exact swap_ne_swap_xy x y b a hxy hby hbx
  | a :: b :: c :: tail =>
    have hab : a ≠ b := by
      intro h; subst h; simp [List.nodup_cons] at hnd
    have hax : a ≠ x := by intro h; subst h; apply hx; simp
    have hay : a ≠ y := by intro h; subst h; apply hy; simp
    have hbx : b ≠ x := by intro h; subst h; apply hx; simp
    have hby : b ≠ y := by intro h; subst h; apply hy; simp
    have hnd_short : (a :: c :: tail).Nodup := by
      simp only [List.nodup_cons, List.mem_cons] at hnd ⊢; tauto
    have hlen_short : (a :: c :: tail).length ≥ 2 := by simp
    have hx_short : x ∉ (a :: c :: tail) := by
      simp only [List.mem_cons] at hx ⊢; tauto
    have hy_short : y ∉ (a :: c :: tail) := by
      simp only [List.mem_cons] at hy ⊢; tauto
    have ih := keelerSeq_nodup (a :: c :: tail) x y
                 hnd_short hlen_short hx_short hy_short hxy
    have hb_short : b ∉ (a :: c :: tail) := by
      simp only [List.nodup_cons, List.mem_cons] at hnd ⊢; tauto
    -- keelerSeq(long) inserts swap x b into keelerSeq(short)
    -- keelerSeq(short) = swap x a :: seqTail
    -- keelerSeq(long)  = swap x a :: swap x b :: seqTail
    -- IH: (swap x a :: seqTail).Nodup
    -- Need: swap x b ∉ (swap x a :: seqTail) ∧ (swap x a :: seqTail).Nodup
    have hk : (b :: c :: tail).getLastD a = (c :: tail).getLastD a := by
      simp [List.getLastD]
    have hd : (b :: c :: tail).dropLast = b :: (c :: tail).dropLast := by
      simp [List.dropLast]
    -- Express keelerSeq(long) and keelerSeq(short) explicitly
    have h_long : keelerSeq (a :: b :: c :: tail) x y =
      swap x a :: swap x b :: ((c :: tail).dropLast.map (swap x) ++
        [swap y ((c :: tail).getLastD a), swap x ((c :: tail).getLastD a), swap y a]) := by
      unfold keelerSeq; dsimp; rw [hk];
    have h_short : keelerSeq (a :: c :: tail) x y =
      swap x a :: ((c :: tail).dropLast.map (swap x) ++
        [swap y ((c :: tail).getLastD a), swap x ((c :: tail).getLastD a), swap y a]) := by
      unfold keelerSeq; dsimp

    -- Set seqTail
    set seqTail := (c :: tail).dropLast.map (swap x) ++
      [swap y ((c :: tail).getLastD a), swap x ((c :: tail).getLastD a), swap y a]
    -- IH in terms of seqTail
    have ih' : (swap x a :: seqTail).Nodup := by rw [← h_short]; exact ih

    -- swap x b ≠ swap x a
    have hba_swap : swap x b ≠ swap x a := by
      intro h; exact hab.symm (swap_right_injective x h)
    -- swap x b ∉ seqTail: uses auxiliary and short-cycle freshness
    have hb_tail : swap x b ∉ seqTail := by
      simp only [seqTail, List.mem_append, List.mem_map, List.mem_cons,
                 List.mem_nil_iff, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ⟨a', ha', h⟩
        have := swap_right_injective x h
        subst this
        exact hb_short (List.mem_cons_of_mem _ (List.dropLast_subset _ ha'))
      · exact swap_ne_swap_xy x y b _ hxy hby hbx
      · intro h
        have := swap_right_injective x h
        subst this
        exact hb_short (List.mem_cons_of_mem _ (getLastD_cons_mem a c tail))
      · exact swap_ne_swap_xy x y b a hxy hby hbx

    rw [h_long, List.nodup_cons]
    exact ⟨by simp only [List.mem_cons, not_or]; exact ⟨Ne.symm hba_swap, (List.nodup_cons.mp ih').1⟩,
           by rw [List.nodup_cons]; exact ⟨hb_tail, (List.nodup_cons.mp ih').2⟩⟩
  termination_by l.length


private def evalCycle (cycle : List Nat) (x y : Nat) : List Nat :=
  let σ := (keelerSeq cycle x y).prod * formPerm cycle
  (List.range (max x y + 1)).map fun i => σ i

#eval evalCycle [5, 1, 2, 3, 4] 6 7
-- Expected: [0, 1, 2, 3, 4, 5, 7, 6]

--  arbitrary permutations

-- **Keeler's Theorem (Futurama Theorem)**
theorem keeler_theorem (σ : Perm α) (x y : α)
    (hx : x ∉ σ.support) (hy : y ∉ σ.support) (hxy : x ≠ y) :
    ∃ (ts : List (Perm α)),
      ts.prod * σ = 1 ∧
      (∀ t ∈ ts, ∃ a : α, t = swap x a ∨ t = swap y a) ∧
      ts.Nodup := by
  -- Step 1: Decompose σ into disjoint cycles c₁, ..., cᵣ via σ.cycleFactorsFinset
  -- Step 2: Convert each cycle cᵢ to a list lᵢ (from its support), with cᵢ = formPerm lᵢ
  -- Step 3: x ∉ lᵢ and y ∉ lᵢ for each i (since x, y ∉ σ.support and lᵢ ⊆ σ.support)
  -- Step 4: Apply keeler_identity to each lᵢ: keelerSeq(lᵢ).prod * formPerm(lᵢ) = swap x y
  -- Step 5: Concatenate all keelerSeqs: ts = Sᵣ ++ ... ++ S₁
  -- Step 6: Product gives ts.prod * σ = (swap x y)ʳ where r = number of cycles
  -- Step 7: If r even, (swap x y)ʳ = 1, done. If r odd, append one swap x y to ts.
  -- Step 8: Each t ∈ ts involves x or y (from keelerSeq_uses_auxiliary per cycle)
  -- Step 9: ts.Nodup (we likely need one more lemma to show that keelerSeqs for disjoint cycles have no transpositions in common)
  sorry
