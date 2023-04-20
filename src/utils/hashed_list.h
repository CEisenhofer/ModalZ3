#pragma once
#include <unordered_map>
#include <vector>

#include <utility>
#include <type_traits>

#include "assertion.h"

// Intention:
// O(n) iteration, O(1) insertion, O(1) deletion

template<typename T>
struct identity {
    T operator()(const T& t) const {
        return t;
    }
};

template<typename T, typename SUBSET_FCT = identity<T>, typename SUBSET = T, class Hash = std::hash<SUBSET>, class Eq = std::equal_to<SUBSET>>
class hashed_list {

    std::vector<T> m_elements;
    std::unordered_map<SUBSET, unsigned, Hash, Eq> m_key_to_idx;

public:

    bool add(T elem) {
        SUBSET subset = SUBSET_FCT()(elem);
        if (contains(subset))
            return false;
        std::pair<SUBSET, unsigned> insert(subset, (unsigned)m_elements.size());
        m_key_to_idx.insert(insert);
        m_elements.push_back(std::move(elem));
        return true;
    }

    unsigned size() const {
        return m_elements.size();
    }

    bool empty() const {
        return size() == 0;
    }

    // Might invalidate indices >= idx
    void remove_at(unsigned idx) {
        SASSERT(m_key_to_idx.size() == m_elements.size());
        SASSERT(idx < m_elements.size());

        SUBSET_FCT fct = SUBSET_FCT();
        SUBSET to_remove = fct(std::move(m_elements[idx]));
        m_elements[idx] = m_elements.back();
        m_key_to_idx[fct(m_elements.back())] = idx;
        m_key_to_idx.erase(to_remove);
        m_elements.pop_back();
    }

    bool contains(const SUBSET& elem) const {
        return m_key_to_idx.contains(elem);
    }

    // Might invalidate indices
    void remove(const SUBSET& elem) {
        SASSERT(contains(elem));
        return remove_at(m_key_to_idx.at(elem));
    }

    T& operator[](unsigned idx) {
        return m_elements[idx];
    }

    T& back() {
        return m_elements.back();
    }

    const std::vector<T>& get_vector() const {
        return m_elements;
    }
};
