#pragma once
#include <unordered_map>
#include <vector>

#include "assertion.h"

// Intention:
// O(n) iteration, O(1) insertion, O(1) deletion

template<typename T>
class hashed_list {

    std::vector<T> m_elements;
    std::unordered_map<T, unsigned> m_key_to_idx;

public:

    void add(T elem) {
        std::pair<T, unsigned> insert(elem, (unsigned)m_elements.size());
        m_key_to_idx.insert(insert);
        m_elements.push_back(std::move(elem));
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

        auto to_remove = std::move(m_elements[idx]);
        m_elements[idx] = m_elements.back();
        m_key_to_idx[m_elements.back()] = idx;
        m_key_to_idx.erase(to_remove);
        m_elements.pop_back();
    }

    bool contains(const T& elem) const {
        return m_key_to_idx.contains(elem);
    }

    // Might invalidate indices
    void remove(const T& elem) {
        SASSERT(contains(elem));
        return remove_at(m_key_to_idx.at(elem));
    }

    T& operator[](unsigned idx) {
        return m_elements[idx];
    }

    T& back() {
        return m_elements.back();
    }
};
