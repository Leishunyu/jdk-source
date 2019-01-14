/*
 * Copyright (C) 2009-2018 Hangzhou FanDianEr Technology Co., Ltd. All rights reserved
 */
package java.test;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * TestAtomicInteger
 *
 * @author huaifeng
 * @since 2019-01-12
 */
public class TestAtomicInteger {
    public static void main(String[] args) {
        AtomicInteger atomicInteger = new AtomicInteger();
        System.out.println(atomicInteger.compareAndSet(0,1));

    }
}
